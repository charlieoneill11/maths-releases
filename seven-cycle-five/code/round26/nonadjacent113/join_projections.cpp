#include "gap_modes.hpp"
#include <set>
struct Layout {
  int first, second, motion, intersectionSize;
  array<int, 3> starts;
};
struct Band {
  int id;
  array<int, 6> cuts{};
  Mask x{}, y{};
};
inline int countBits(Mask q) { return __builtin_popcountll(q); }
int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  readAtlas(argv[1]);
  buildCutIndex();
  buildSingleLayers();
  vector<Layout> cases;
  ifstream input(argv[2]);
  if (!input)
    throw runtime_error("missing layout ledger");
  Layout q;
  string line;
  while (getline(input, line)) {
    istringstream row(line);
    string extra;
    if (!(row >> q.first >> q.second >> q.motion >> q.intersectionSize >>
          q.starts[0] >> q.starts[1] >> q.starts[2]) ||
        row >> extra || q.first < 0 || q.first >= 1016 || q.second < 0 ||
        q.second >= 1016 || q.motion < 0 || q.motion >= 16464)
      throw runtime_error("invalid layout record");
    cases.push_back(q);
  }
  if (!input.eof())
    throw runtime_error("layout input failed");
  unordered_map<Mask, vector<int>> indices;
  for (auto &q : cases) {
    auto l = imageCuts(q.first, 0), r = imageCuts(q.second, q.motion);
    for (int a = 0; a < 3; a++)
      for (int j = 0; j < 2; j++) {
        int t = markedStart(q.starts[a], j);
        indices[contactKey(l[a][t], r[a][t])];
      }
  }
  // Materialize every atlas projection realizing both marked A contacts.
  for (int b = 0; b < 1016; b++)
    for (int g = 0; g < 16464; g++) {
      auto &d = motionAxes[g];
      int sourceAxis = d.sourceAxis[0], planeMotion = d.plane[0],
          shift = d.shift[0], sign = d.sign[0];
      int t = mod(-sign * shift - (sign < 0)), t2 = mod(t + 2 * sign);
      int m1 = movedCuts[baseCuts[b][sourceAxis][t]][planeMotion],
          m2 = movedCuts[baseCuts[b][sourceAxis][t2]][planeMotion];
      auto it = indices.find(contactKey(m1, m2));
      if (it != indices.end())
        it->second.push_back(b * 16464 + g);
    }
  long long totals = 0, passedLayouts = 0, prefixes = 0;
  ofstream output(argv[3]);
  if (!output)
    throw runtime_error("cannot write products");
  for (auto &q : cases) {
    auto l = imageCuts(q.first, 0), r = imageCuts(q.second, q.motion);
    auto &left = atlasSites[q.first];
    Sites right;
    for (int i = 0; i < 33; i++)
      right[i] = motions[q.motion][atlasSites[q.second][i]];
    array<Mask, 33> conflict{};
    for (int i = 0; i < 33; i++)
      for (int j = 0; j < 33; j++) {
        bool near = true;
        for (int f : {49, 7, 1}) {
          int d = mod((left[i] / f) % 7 - (right[j] / f) % 7);
          if (d >= 2 && d <= 5)
            near = false;
        }
        if (near)
          conflict[i] |= Mask(1) << j;
      }
    auto middleIndependent = [&](Mask x, Mask y) {
      for (; x; x &= x - 1)
        if (conflict[__builtin_ctzll(x)] & y)
          return false;
      return true;
    };
    vector<Band> domains[6];
    array<Mask, 6> leftCoverage{}, rightCoverage{};
    for (int j = 0; j < 6; j++) {
      int a = j / 2, t = markedStart(q.starts[a], j % 2);
      Mask lift[2][49]{};
      for (int s = 0; s < 2; s++)
        for (int i = 0; i < 33; i++) {
          int pt = s ? right[i] : left[i];
          int w[] = {pt / 49, pt / 7 % 7, pt % 7};
          if (mod(w[a] - t) > 1)
            continue;
          int f = 0;
          for (int z = 0; z < 3; z++)
            if (z != a)
              f = f * 7 + w[z];
          Mask bit = Mask(1) << i;
          lift[s][f] = bit;
          (s ? rightCoverage : leftCoverage)[j] |= bit;
        }
      auto &available = indices[contactKey(l[a][t], r[a][t])];
      set<Planes> stored;
      for (int id : available) {
        int b = id / 16464, g = id % 16464;
        auto &d = motionAxes[g];
        Planes layers;
        for (int yy = 0; yy < 7; yy++)
          layers[yy] = layerMask(b, d, yy);
        if (!stored.insert(layers).second)
          continue;
        Band v;
        v.id = id;
        for (Mask m = layers[1]; m; m &= m - 1)
          v.x |= lift[0][__builtin_ctzll(m)];
        for (Mask m = layers[2]; m; m &= m - 1)
          v.y |= lift[1][__builtin_ctzll(m)];
        auto c = imageCuts(b, g);
        for (int k = 0; k < 6; k++)
          if (k / 2 != a) {
            int e = k / 2, axis = 1 + e - (e > a),
                tt = markedStart(q.starts[e], k % 2);
            v.cuts[k] = c[axis][tt];
          }
        if (middleIndependent(v.x, v.y))
          domains[j].push_back(v);
      }
    }
    array<int, 6> order{0, 1, 2, 3, 4, 5}, chosen;
    sort(order.begin(), order.end(),
         [&](int a, int b) { return domains[a].size() < domains[b].size(); });
    long long productCount = 0;
    auto dfs = [&](auto &&self, int s, Mask seenLeft, Mask seenRight, Mask x,
                   Mask y) -> void {
      if (s == 6) {
        productCount++;
        output << q.first << ' ' << q.second << ' ' << q.motion << ' '
               << q.intersectionSize;
        for (auto a : q.starts)
          output << ' ' << a;
        for (int i = 0; i < 6; i++)
          output << ' ' << domains[i][chosen[i]].id;
        output << '\n';
        output.flush();
        return;
      }
      int j = order[s];
      for (int n = 0; n < (int)domains[j].size(); n++) {
        auto &v = domains[j][n];
        if (((v.x ^ x) & seenLeft & leftCoverage[j]) ||
            ((v.y ^ y) & seenRight & rightCoverage[j]))
          continue;
        bool ok = true;
        for (int h = 0; h < s; h++) {
          int k = order[h];
          if (j / 2 != k / 2 && domains[k][chosen[k]].cuts[j] != v.cuts[k]) {
            ok = false;
            break;
          }
        }
        if (!ok || !middleIndependent(x | v.x, y | v.y))
          continue;
        chosen[j] = n;
        prefixes++;
        self(self, s + 1, seenLeft | leftCoverage[j],
             seenRight | rightCoverage[j], x | v.x, y | v.y);
      }
    };
    dfs(dfs, 0, 0, 0, 0, 0);
    totals += productCount;
    if (productCount)
      passedLayouts++;
  }
  output.close();
  if (!output)
    throw runtime_error("product output failed");
  cout << "layouts " << cases.size() << " compatible prefixes " << prefixes
       << " surviving layouts " << passedLayouts
       << " eight-projection products " << totals << endl;
}
