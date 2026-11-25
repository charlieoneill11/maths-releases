// Exhaust all choices of eight 33-bands with the two starts on each axis
// at cyclic distance three. All planar masks have ordered physical coordinates.
#include "atlas.hpp"
#include <numeric>

using Key = array<MaskId, 6>;
constexpr int imageCount = 16464, phaseCount = 343;
// A transverse atlas image lists the source axis first, followed by the
// other two remaining axes in their original order.
int crossingSlot(int band, int other) {
  int axis = band / 2, otherAxis = other / 2;
  assert(axis != otherAxis);
  return 2 * (1 + otherAxis - (otherAxis > axis)) + other % 2;
}

int main(int argc, char **argv) {
  if (argc != 2 && argc != 4) {
    cerr << "Usage: gap_three ATLAS.tsv [FIRST_REP END_REP]\n";
    return 2;
  }
  int firstClass = argc == 4 ? stoi(argv[2]) : 0,
      endClass = argc == 4 ? stoi(argv[3]) : 1016;
  if (firstClass < 0 || firstClass > endClass || endClass > 1016)
    return 2;
  readAtlas(argv[1]);
  buildCutIndex();
  int maskCount = planar.size();
  vector<vector<MaskId>> partners(maskCount);
  int numImages = 1016 * imageCount;
  vector<Key> all(numImages);
  // Descriptions (b, g) and (b, h) of a support are the same physical set
  // exactly when g and h differ by an element of the stabiliser of class b.
  // firstMotion maps each description to the least motion giving its set.
  vector<uint16_t> firstMotion(numImages);
  vector<int> stabiliser(1016);
  {
    vector<Image> v(imageCount);
    long long orbitTotal = 0;
    for (int b = 0; b < 1016; b++) {
      for (int g = 0; g < imageCount; g++) {
        SupportBits im{};
        for (int i : atlasSites[b]) {
          int k = motions[g][i];
          im[k / 64] |= Mask(1) << (k % 64);
        }
        v[g] = {im, uint16_t(g)};
      }
      sort(v.begin(), v.end(), [](const Image &x, const Image &y) {
        return x.bits != y.bits ? x.bits < y.bits : x.motion < y.motion;
      });
      int distinct = 0;
      uint16_t lead = 0;
      for (int i = 0; i < imageCount; i++) {
        if (i == 0 || v[i].bits != v[i - 1].bits) {
          distinct++;
          lead = v[i].motion;
        }
        firstMotion[b * imageCount + v[i].motion] = lead;
      }
      if (imageCount % distinct)
        throw runtime_error("orbit size does not divide the group order");
      stabiliser[b] = imageCount / distinct;
      orbitTotal += distinct;
    }
    array<int, 7> byOrder{};
    for (int b = 0; b < 1016; b++)
      if (stabiliser[b] < 7)
        byOrder[stabiliser[b]]++;
    if (orbitTotal != 16672544 || byOrder[1] != 1011 || byOrder[2] != 1 ||
        byOrder[3] != 3 || byOrder[6] != 1)
      throw runtime_error("unexpected orbit sizes");
  }
  array<vector<int>, 3> maskOffsets, imagesByMask;
  for (int j = 0; j < 3; j++)
    maskOffsets[j].assign(maskCount + 1, 0);
  for (int b = 0; b < 1016; b++)
    for (int g = 0; g < imageCount; g++) {
      auto &key = all[b * imageCount + g];
      auto &d = motionAxes[g];
      for (int a = 0; a < 3; a++)
        for (int s : {0, 1}) {
          int t = 3 * s;
          int u = mod(d.sign[a] * (t - d.shift[a]) - (d.sign[a] < 0));
          MaskId m = movedCuts[baseCuts[b][d.sourceAxis[a]][u]][d.plane[a]];
          key[2 * a + s] = m;
          if (2 * a + s < 3)
            maskOffsets[2 * a + s][1 + m]++;
        }
    }
  // Construct ordered gap-three edges from the two cuts of each actual image.
  for (const auto &key : all)
    partners[key[0]].push_back(key[1]);
  for (auto &row : partners) {
    sort(row.begin(), row.end());
    row.erase(unique(row.begin(), row.end()), row.end());
  }
  assert(maskCount == 138670);
  // Validate the indexing against direct physical coordinates for every pair
  // of a representative and a motion, that is, for all 1016 * 16464 images.
  long long validated = 0;
  for (int b = 0; b < 1016; b++)
    for (int g = 0; g < imageCount; g++) {
      array<Mask, 6> direct{};
      for (int p : atlasSites[b]) {
        int v = motions[g][p];
        array<int, 3> z{v / 49, v / 7 % 7, v % 7};
        for (int a = 0; a < 3; a++)
          for (int side = 0; side < 2; side++)
            if (mod(z[a] - 3 * side) < 2) {
              int q = 0;
              for (int t = 0; t < 3; t++)
                if (t != a)
                  q = 7 * q + z[t];
              direct[2 * a + side] |= Mask(1) << q;
            }
      }
      for (int j = 0; j < 6; j++) {
        auto it = planar.find(direct[j]);
        if (it == planar.end() || it->second != all[b * imageCount + g][j])
          throw runtime_error("cut index differs from direct coordinates");
      }
      validated++;
    }
  if (validated != numImages)
    throw runtime_error("incomplete direct-coordinate validation");
  cout << "Direct coordinates agree with the cut index for all " << validated
       << " class-motion pairs" << endl;
  for (int j = 0; j < 3; j++) {
    auto &q = maskOffsets[j];
    for (int i = 0; i < maskCount; i++)
      q[i + 1] += q[i];
    imagesByMask[j].resize(numImages);
    auto pos = q;
    for (int i = 0; i < numImages; i++)
      imagesByMask[j][pos[all[i][j]]++] = i;
  }
  vector<int> candidateCount(maskCount);
  for (int m = 0; m < maskCount; m++)
    for (auto u : partners[m])
      candidateCount[m] += maskOffsets[0][1 + u] - maskOffsets[0][u];
  array<vector<int>, 6> allowedAt;
  for (auto &t : allowedAt)
    t.resize(maskCount);
  vector<int> base(maskCount + 1);
  for (int j = 0; j < maskCount; j++)
    base[j + 1] = base[j] + partners[j].size();
  auto edgeId = [&](int a, int b) {
    auto &v = partners[a];
    auto it = lower_bound(v.begin(), v.end(), MaskId(b));
    assert(it != v.end() && *it == MaskId(b));
    return base[a] + int(it - v.begin());
  };
  int edgeCount = base[maskCount];
  assert(edgeCount == 4145792);
  vector<int> edgeIndex(numImages), edgeOffset(edgeCount + 1),
      edgeIds(numImages);
  for (int i = 0; i < numImages; i++) {
    int e = edgeIndex[i] = edgeId(all[i][0], all[i][1]);
    edgeOffset[e + 1]++;
  }
  partial_sum(edgeOffset.begin(), edgeOffset.end(), edgeOffset.begin());
  {
    auto pos = edgeOffset;
    for (int i = 0; i < numImages; i++)
      edgeIds[pos[edgeIndex[i]]++] = i;
  }
  long long survived = 0;
  vector<array<uint64_t, 4>> signatures(edgeCount);
  vector<int> lastClass(edgeCount);
  for (int id = 0; id < numImages; id++) {
    int e = edgeIndex[id];
    lastClass[e] = id / imageCount;
    for (int d = 0; d < 4; d++) {
      uint32_t m = all[id][2 + d] * 2654435761u;
      signatures[e][d] |= 1ull << (m >> 26);
    }
  }
  vector<int>().swap(edgeIndex);
  // Each of the other six full bands has its two cuts on the first axis
  // fixed by the two source supports. A nonempty common signature bit is
  // necessary for two such domains to share an exact planar mask. The search
  // checks the full mask IDs, including every transverse edge.
  auto testSixBands = [&](int root, int second) {
    int edge[6], sizes[6], chosen[6];
    array<int, 6> orderBySize{0, 1, 2, 3, 4, 5};
    for (int a = 0; a < 6; a++) {
      edge[a] = edgeId(all[root][a], all[second][a]);
      if (lastClass[edge[a]] < root / imageCount)
        return;
      sizes[a] = edgeOffset[edge[a] + 1] - edgeOffset[edge[a]];
    }
    for (int a = 0; a < 6; a++)
      for (int b = 0; b < a; b++)
        if (a / 2 != b / 2) {
          int ba = crossingSlot(a, b) - 2, ab = crossingSlot(b, a) - 2;
          if (!(signatures[edge[a]][ba] & signatures[edge[b]][ab]))
            return;
        }
    sort(orderBySize.begin(), orderBySize.end(),
         [&](int l, int h) { return sizes[l] < sizes[h]; });
    auto visit = [&](auto &&self, int t) -> bool {
      if (t == 6)
        return true;
      int a = orderBySize[t];
      for (int h = edgeOffset[edge[a]]; h < edgeOffset[edge[a] + 1]; h++) {
        int x = edgeIds[h];
        if (x / imageCount < root / imageCount)
          continue;
        auto &u = all[x];
        bool consistent = true;
        for (int jj = 0; jj < t; jj++) {
          int b = orderBySize[jj];
          if (a / 2 == b / 2)
            continue;
          if (u[crossingSlot(a, b)] != all[chosen[b]][crossingSlot(b, a)]) {
            consistent = false;
            break;
          }
        }
        if (!consistent)
          continue;
        chosen[a] = x;
        if (self(self, t + 1))
          return true;
      }
      return false;
    };
    bool ok = visit(visit, 0);
    if (ok) {
      survived++;
      int rec[8] = {root, second};
      copy(chosen, chosen + 6, rec + 2);
      cerr << "eight-band witness";
      for (int id : rec)
        cerr << " " << id;
      cerr << "\n";
    }
  };
  // Both search indexes use slot zero as the first key. Slot one is its
  // parallel mate. Slot two belongs to a different transverse axis.
  struct Slice {
    uint32_t m;
    int begin;
  };
  array<vector<Slice>, 2> groups;
  array<vector<int>, 2> groupOffsets, elements;
  for (int indexType = 0; indexType < 2; indexType++) {
    int secondSlot = 1 + indexType;
    auto &orderByPair = elements[indexType];
    orderByPair.resize(numImages);
    auto off0 = maskOffsets[0];
    for (int id : imagesByMask[secondSlot])
      orderByPair[off0[all[id][0]]++] = id;
    auto &slices = groups[indexType];
    auto &offsets = groupOffsets[indexType];
    offsets.resize(maskCount + 1);
    slices.reserve(numImages);
    for (int m = 0; m < maskCount; m++) {
      offsets[m] = slices.size();
      uint32_t prev = ~0u;
      for (int t = maskOffsets[0][m]; t < maskOffsets[0][m + 1]; t++) {
        auto x = all[orderByPair[t]][secondSlot];
        if (x != prev) {
          slices.push_back({x, t});
          prev = x;
        }
      }
    }
    offsets[maskCount] = slices.size();
    slices.push_back({0, numImages});
  }
  for (auto &v : imagesByMask)
    vector<int>().swap(v);
  for (auto &v : maskOffsets)
    vector<int>().swap(v);
  vector<int> permId(27, -1);
  array<int, 3> pi{0, 1, 2};
  int piNum = 0;
  do {
    permId[9 * pi[0] + 3 * pi[1] + pi[2]] = piNum++;
  } while (next_permutation(pi.begin(), pi.end()));

  unsigned long long survivingPhases = 0, visits = 0, hits = 0, emptyPhases = 0;
  unsigned long long distinctPairs = 0;
  vector<unsigned long long> hitsByClass(1016), distinctByClass(1016);
  vector<int> passed;
  int phases = 0;
  // A least atlas class among all eight supports can be moved to the first
  // band. Only the 343 translations of that representative are needed,
  // since signed permutations can be performed by permuting axes and acting by
  // x -> 4-x, which exchanges the two designated bands on that axis.
  for (int b = firstClass; b < endClass; b++)
    for (int g = 0; g < phaseCount; g++) {
      const auto &original = all[b * imageCount + g];
      ++phases;
      array<int, 6> chosen{0, 1, 2, 3, 4, 5};
      sort(chosen.begin(), chosen.end(), [&](int i, int j) {
        return candidateCount[original[i]] < candidateCount[original[j]];
      });
      int f = chosen[0], s = chosen[1];
      int indexType = (f / 2 != s / 2), secondSlot = 1 + indexType;
      int perm[3] = {f / 2, -1, -1};
      if (indexType)
        perm[1] = s / 2;
      for (int j = 1; j < 3; j++)
        if (perm[j] < 0)
          for (int a = 0; a < 3; a++)
            if (find(perm, perm + 3, a) == perm + 3) {
              perm[j] = a;
              break;
            }
      // Move the two least expensive query slots to the two keys of one index.
      // This additional symmetry only changes the physical coordinate frame.
      int flip = (f % 2) | ((indexType ? s % 2 : 0) << 1);
      int shift[3] = {g / 49, g / 7 % 7, g % 7};
      int tr = 0;
      for (int a = 0; a < 3; a++)
        tr = 7 * tr +
             ((flip >> a & 1) ? mod(4 - shift[perm[a]]) : shift[perm[a]]);
      int root = imageCount * b +
                 phaseCount *
                     (8 * permId[9 * perm[0] + 3 * perm[1] + perm[2]] + flip) +
                 tr;
      const auto &k = all[root];
      assert(candidateCount[k[0]] == candidateCount[original[f]]);
      assert(candidateCount[k[secondSlot]] == candidateCount[original[s]]);

      array<int, 6> order{0, 1, 2, 3, 4, 5};
      sort(order.begin(), order.end(), [&](int i, int j) {
        return candidateCount[k[i]] < candidateCount[k[j]];
      });
      for (int h = 0; h < 6; h++)
        for (auto x : partners[k[h]])
          allowedAt[h][x] = phases;
      auto &orderByPair = elements[indexType];
      auto &slices = groups[indexType];
      auto &offsets = groupOffsets[indexType];
      long long ok = 0;
      passed.clear();
      // The group already realizes two allowed edges. Check all four other
      // edges before opening the exact six-domain search.
      auto visitGroup = [&](int index) {
        for (int q = slices[index].begin; q < slices[index + 1].begin; q++) {
          visits++;
          int id = orderByPair[q];
          if (id / imageCount < b)
            continue;
          auto &v = all[id];
          bool good = true;
          for (int d : order)
            if (d != 0 && d != secondSlot && allowedAt[d][v[d]] != phases) {
              good = false;
              break;
            }
          if (good) {
            ok++;
            hitsByClass[id / imageCount]++;
            passed.push_back(id - id % imageCount + firstMotion[id]);
            testSixBands(root, id);
          }
        }
      };
      for (auto x : partners[k[0]]) {
        int l = offsets[x], r = offsets[x + 1];
        if (6 * partners[k[secondSlot]].size() < size_t(r - l)) {
          for (auto u : partners[k[secondSlot]]) {
            int h = lower_bound(slices.begin() + l, slices.begin() + r, u,
                                [](const Slice &group, MaskId mask) {
                                  return group.m < mask;
                                }) -
                    slices.begin();
            if (h < r && slices[h].m == u)
              visitGroup(h);
          }
        } else {
          for (int h = l; h < r; h++)
            if (allowedAt[secondSlot][slices[h].m] == phases)
              visitGroup(h);
        }
      }
      survivingPhases += ok > 0;
      emptyPhases += ok == 0;
      hits += ok;
      // Count the distinct physical supports T for this S.
      sort(passed.begin(), passed.end());
      for (size_t i = 0; i < passed.size(); i++)
        if (i == 0 || passed[i] != passed[i - 1]) {
          distinctPairs++;
          distinctByClass[passed[i] / imageCount]++;
        }
      if (phases % phaseCount == 0)
        cout << b << " " << survivingPhases << " " << emptyPhases << " "
             << visits << " " << hits << " cliques " << survived << " "
             << "phases " << phases << " distinct " << distinctPairs << endl;
    }
  cout << "Summary: " << phases << " phases, " << hits << " six-contact pairs, "
       << survived << " pairs admitting all eight projections.\n";
  // Every description of a support passes or fails with it, so each class
  // contributes its stabiliser order times its number of distinct supports.
  cout << "Distinct six-contact pairs " << distinctPairs << ", repeated descriptions "
       << hits - distinctPairs << " in the classes";
  for (int c = 0; c < 1016; c++) {
    if (hitsByClass[c] != stabiliser[c] * distinctByClass[c])
      throw runtime_error("descriptions of a class are not stabiliser multiples");
    if (hitsByClass[c] != distinctByClass[c])
      cout << " " << c << " (stabiliser " << stabiliser[c] << ", "
           << hitsByClass[c] - distinctByClass[c] << ")";
  }
  cout << endl;
  if (firstClass == 0 && endClass == 1016) {
    assert(phases == 348488 && survivingPhases == 204922 &&
           emptyPhases == 143566);
    assert(hits == 21633276 && survived == 0);
    assert(distinctPairs == 21378687);
  }
  return survived != 0;
}
