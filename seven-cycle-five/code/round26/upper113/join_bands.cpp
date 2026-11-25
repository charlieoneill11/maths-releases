#include "middle_record.hpp"
#include "prefixes.hpp"

struct Geometry {
  array<Mask, 4> outer;
  array<array<MaskId, 7>, 2> cuts;
};
struct Hash {
  size_t operator()(const Prefix &p) const noexcept {
    return mix(p[0]) ^ (mix(p[1]) * 7) ^ (mix(p[2]) * 13);
  }
};
unordered_map<Prefix, int, Hash> domainIndex;
vector<vector<int>> domains;
vector<Geometry> geometry;
vector<int> geometryIndex;
vector<int> imageId;
// Resolve full atlas supports from exact three-level prefixes. A cached
// domain stores every matching image, even when several have the same prefix.
int getDomain(const Prefix &key) {
  auto [it, fresh] = domainIndex.emplace(key, domainIndex.size());
  if (!fresh)
    return it->second;
  auto &out = domains.emplace_back();
  for (int id = buckets[prefixBucket(key)]; id >= 0; id = nextImage[id]) {
    int b = id / 16464, g = id % 16464;
    if (prefix(b, g) != key)
      continue;
    int idx = geometryIndex[id];
    if (idx < 0) {
      idx = geometryIndex[id] = geometry.size();
      auto &v = geometry.emplace_back();
      imageId.push_back(id);
      const auto &d = motionAxes[g];
      for (int h = 3; h < 7; h++)
        v.outer[h - 3] = layerMask(b, d, h);
      for (int a = 1; a <= 2; a++)
        for (int t = 0; t < 7; t++) {
          int s = d.sign[a], u = mod(s * (t - d.shift[a]) - (s < 0));
          v.cuts[a - 1][t] =
              movedCuts[baseCuts[b][d.sourceAxis[a]][u]][d.plane[a]];
        }
    }
    out.push_back(idx);
  }
  assert(!out.empty());
  return it->second;
}
struct Search {
  Distances gaps{};
  int starts[6], ids[6], knownOnCenter[3], chosen[6];
  bool compatible(int j, int p, int k, int q) const {
    const auto &x = geometry[p];
    const auto &y = geometry[q];
    int a = j / 2, b = k / 2;
    if (a == b) {
      if (gaps[a] != 1)
        return true;
      // Only the remaining four first-axis levels can augment the known shared
      // level. Their common support bounds the number of possible additional
      // words.
      int n = knownOnCenter[a];
      for (int h = 0; h < 4; h++)
        n += __builtin_popcountll(x.outer[h] & y.outer[h]);
      return n >= 16;
    }
    return x.cuts[b - (b > a)][starts[k]] == y.cuts[a - (a > b)][starts[j]];
  }
  bool solve() {
    array<int, 6> order{0, 1, 2, 3, 4, 5};
    sort(order.begin(), order.end(), [&](int a, int b) {
      return domains[ids[a]].size() < domains[ids[b]].size();
    });
    // Test necessary two-band contacts before the six-way join.
    for (int p = 0; p < 6; p++)
      for (int q = p + 1; q < 6; q++) {
        int j = order[p], k = order[q];
        bool pair = false;
        for (int x : domains[ids[j]]) {
          for (int y : domains[ids[k]])
            if (compatible(j, x, k, y)) {
              pair = true;
              break;
            }
          if (pair)
            break;
        }
        if (!pair)
          return false;
      }
    auto dfs = [&](auto &&self, int p) -> bool {
      if (p == 6)
        return true;
      int j = order[p];
      for (int x : domains[ids[j]]) {
        bool ok = true;
        for (int i = 0; i < p; i++)
          if (!compatible(j, x, order[i], chosen[order[i]])) {
            ok = false;
            break;
          }
        if (ok) {
          chosen[j] = x;
          if (self(self, p + 1))
            return true;
        }
      }
      return false;
    };
    return dfs(dfs, 0);
  }
};
struct Record {
  MiddleChoice j;
  array<uint32_t, 6> ids;
};
int main(int argc, char **argv) {
  if (argc != 6)
    return 2;
  int klo = atoi(argv[4]), khi = atoi(argv[5]);
  readAtlas(argv[1]);
  buildCutIndex();
  indexFirstThreeLayers();
  geometryIndex.assign(nextImage.size(), -1);
  planarMasks.resize(planar.size());
  for (auto [m, j] : planar)
    planarMasks[j] = m;
  ifstream input(argv[2], ios::binary);
  ofstream output(argv[3], ios::binary);
  MiddleChoice r, last{};
  Mask previousMarkedMiddle = ~Mask(0), tested[34] = {}, unique[34] = {},
       yes[34] = {};
  array<uint32_t, 6> witness{};
  bool lastYes = false, first = true;
  Cuts left{}, right{};
  array<array<Mask, 7>, 3> layerBits{};

  array<array<int, 7>, 3> sharedBase{};

  while (input.read((char *)&r, sizeof r)) {
    if (r.intersectionSize < klo || r.intersectionSize > khi)
      continue;
    tested[r.intersectionSize]++;
    bool newPair = first || r.first != last.first || r.second != last.second ||
                   r.motion != last.motion;
    if (newPair) {
      left = imageCuts(r.first, 0);
      right = imageCuts(r.second, r.motion);
      layerBits = {};
      sharedBase = {};
      for (int n = 0; n < 33; n++) {
        int i = atlasSites[r.first][n], q[3] = {i / 49, i / 7 % 7, i % 7};
        for (int a = 0; a < 3; a++) {
          layerBits[a][q[a]] |= 1ull << n;
          sharedBase[a][q[a]]++;
        }
      }
      for (int i : atlasSites[r.second]) {
        int j = motions[r.motion][i], q[3] = {j / 49, j / 7 % 7, j % 7};
        for (int a = 0; a < 3; a++)
          sharedBase[a][q[a]]++;
      }
    }
    const auto gaps = transverseDistances(r.distanceCode);
    bool newCenter = newPair || r.distanceCode != last.distanceCode ||
                     !equal(r.centers, r.centers + 3, last.centers);
    Mask cover = 0;
    for (int a = 0; a < 3; a++) {
      int gap = gaps[a];
      for (int offset : {-gap, 1 - gap, 0, 1})
        cover |= layerBits[a][mod(r.centers[a] + offset)];
    }
    Mask restricted = r.middle & cover;
    // Unmarked middle bits cannot affect a transverse prefix or the number
    // of prescribed words on a marked shared level.
    if (newCenter || restricted != previousMarkedMiddle) {
      unique[r.intersectionSize]++;
      Search s;
      s.gaps = gaps;
      for (int a = 0; a < 3; a++) {
        s.knownOnCenter[a] =
            sharedBase[a][r.centers[a]] -
            __builtin_popcountll(r.middle & layerBits[a][r.centers[a]]);
        for (int k = 0; k < 2; k++) {
          int j = 2 * a + k,
              t = s.starts[j] = mod(r.centers[a] - (k == 0 ? gaps[a] : 0));
          Mask mid = 0;
          for (Mask z =
                   r.middle & (layerBits[a][t] | layerBits[a][(t + 1) % 7]);
               z; z &= z - 1) {
            int i = atlasSites[r.first][__builtin_ctzll(z)],
                q[3] = {i / 49, i / 7 % 7, i % 7};
            int m = 0;
            for (int e = 0; e < 3; e++)
              if (e != a)
                m = 7 * m + q[e];
            mid |= 1ull << m;
          }
          Mask l = planarMasks[left[a][t]], h = planarMasks[right[a][t]];
          s.ids[j] = getDomain({l ^ mid, mid, h ^ mid});
        }
      }
      lastYes = s.solve();
      if (lastYes)
        for (int j = 0; j < 6; j++)
          witness[j] = imageId[s.chosen[j]];
    }
    if (lastYes) {
      yes[r.intersectionSize]++;
      Record z{r, witness};
      output.write((char *)&z, sizeof z);
    }
    last = r;
    previousMarkedMiddle = restricted;
    first = false;
  }
  output.close();
  if (!input.eof() || input.gcount() || !output)
    throw runtime_error("binary record input or output failed");
  cout << "intersection\tmiddles\tcovered_instances\tsurviving_products\n";
  for (int k = klo; k <= khi; k++)
    cout << k << '\t' << tested[k] << '\t' << unique[k] << '\t' << yes[k]
         << '\n';
  cerr << "distinct domains " << domainIndex.size() << " 33-bands "
       << geometry.size() << '\n';
}
