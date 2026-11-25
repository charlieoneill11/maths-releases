#include "gap_modes.hpp"
#include <set>
struct MiddleLevels {
  Mask x, y;
  bool operator<(const MiddleLevels &o) const {
    return x != o.x ? x < o.x : y < o.y;
  }
  bool operator==(const MiddleLevels &o) const { return x == o.x && y == o.y; }
};
struct Mark {
  Mask l{}, r{};
  vector<MiddleLevels> choices;
};
inline int countBits(Mask m) { return __builtin_popcountll(m); }
int main(int argc, char **argv) {
  if (argc != 5 && argc != 6)
    return 2;
  const string target = argc == 6 ? argv[5] : "113";
  if (target != "112" && target != "113")
    throw runtime_error("expected target 112 or 113");
  const int missingLimit = target == "112" ? 3 : 2;
  const int minimumLevel = target == "112" ? 15 : 14;
  const int maximumLevel = target == "112" ? 15 : 19;
  bool mixed = mixedMode(argv[3]);
  readAtlas(argv[1]);
  buildCutIndex();
  buildSingleLayers();
  std::unordered_map<Mask, vector<MiddleLevels>> allChoices;

  for (int b = 0; b < 1016; b++)
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++) {

        for (int h = 0; h < 392; h++) {
          auto l = movedCuts[baseCuts[b][a][t]][h],
               r = movedCuts[baseCuts[b][a][(t + 2) % 7]][h];
          Mask x = movedLayers[baseLayers[b][a][(t + 1) % 7]][h],
               y = movedLayers[baseLayers[b][a][(t + 2) % 7]][h];
          assert(!(x & y));
          allChoices[contactKey(l, r)].push_back({x, y});
          allChoices[contactKey(r, l)].push_back({y, x});
        }
      }
  for (auto &[k, choices] : allChoices) {
    sort(choices.begin(), choices.end());
    choices.erase(unique(choices.begin(), choices.end()), choices.end());
  }
  cerr << "local keys " << allChoices.size() << endl;
  array<long, 34> pairs{}, places{}, prefixes{}, completed{}, finalPairs{},
      finalLayouts{};
  ifstream in(argv[2], ios::binary);
  ofstream layouts(argv[4]);
  if (!in || !layouts)
    throw runtime_error("cannot access pair or layout file");
  SupportPair rr;

  array<array<bool, 343>, 343> confusable{};
  for (int p = 0; p < 343; p++)
    for (int q = 0; q < 343; q++) {
      bool a = true;
      for (int j : {49, 7, 1}) {
        int z = mod((p / j) % 7 - (q / j) % 7);
        if (z >= 2 && z <= 5)
          a = false;
      }
      confusable[p][q] = a;
    }
  size_t scanned = 0;
  while (in.read((char *)&rr, sizeof rr)) {
    if ((++scanned) % 1000000 == 0)
      cerr << "pairs " << scanned << endl;
    int k = rr.intersectionSize;
    if (k > 33 || rr.first >= 1016 || rr.second >= 1016 || rr.motion >= 16464)
      throw runtime_error("invalid projection pair");
    pairs[k]++;
    auto left = imageCuts(rr.first, 0), right = imageCuts(rr.second, rr.motion);
    array<vector<int>, 3> possibleStarts;
    bool possible = true;
    for (int a = 0; a < 3; a++) {
      bool ok[7];
      for (int t = 0; t < 7; t++)
        ok[t] = allChoices.count(contactKey(left[a][t], right[a][t]));
      for (int t = 0; t < 7; t++)
        for (int d = 0; d < 1 + int(mixed); d++)
          if (ok[t] && ok[(t + 2 + d) % 7])
            possibleStarts[a].push_back(t + 7 * d);
      if (possibleStarts[a].empty()) {
        possible = false;
        break;
      }
    }
    if (!possible)
      continue;
    auto &leftSites = atlasSites[rr.first];
    Sites rightSites;
    for (int i = 0; i < 33; i++)
      rightSites[i] = motions[rr.motion][atlasSites[rr.second][i]];
    array<int, 33> mate;
    mate.fill(-1);
    array<Mask, 33> conflicts{};
    for (int i = 0; i < 33; i++)
      for (int j = 0; j < 33; j++)
        if (confusable[leftSites[i]][rightSites[j]])
          conflicts[i] |= Mask(1) << j;
    // Match each left word to a conflicting right word. The target bounds the
    // number of matched edges that can be empty.
    for (int i = 0; i < 33; i++) {
      Mask visited = 0;
      auto augment = [&](auto &&self, int i) -> bool {
        for (Mask q = conflicts[i] & ~visited; q; q &= q - 1) {
          int j = __builtin_ctzll(q);
          if (visited & (Mask(1) << j))
            continue;
          visited |= Mask(1) << j;
          if (mate[j] < 0 || self(self, mate[j])) {
            mate[j] = i;
            return true;
          }
        }
        return false;
      };
      if (!augment(augment, i))
        throw runtime_error("missing perfect matching between maxima");
    }
    array<array<Mark, 7>, 3> ports;
    for (int a = 0; a < 3; a++) {
      int required = 0;
      for (int u : possibleStarts[a]) {
        int t = u % 7, dist = 2 + u / 7;
        required |= 1 << t | 1 << ((t + dist) % 7);
      }
      for (int t = 0; t < 7; t++)
        if (required >> t & 1) {
          auto &p = ports[a][t];
          Mask localIndex[2][49]{};
          for (int side = 0; side < 2; side++)
            for (int i = 0; i < 33; i++) {
              int v = side ? rightSites[i] : leftSites[i],
                  c[] = {v / 49, v / 7 % 7, v % 7};
              if (mod(c[a] - t) > 1)
                continue;
              int u = 0;
              for (int s = 0; s < 3; s++)
                if (s != a)
                  u = u * 7 + c[s];
              Mask bit = Mask(1) << (side ? mate[i] : i);
              localIndex[side][u] = bit;
              (side ? p.r : p.l) |= bit;
            }
          auto tr = [&](int side, Mask m) {
            Mask z = 0;
            for (; m; m &= m - 1)
              z |= localIndex[side][__builtin_ctzll(m)];
            return z;
          };
          for (auto [x, y] : allChoices[contactKey(left[a][t], right[a][t])]) {
            Mask m = tr(0, x), n = tr(1, y);
            if (!(m & n) && countBits(p.l & p.r & ~(m | n)) <= missingLimit)
              p.choices.push_back({m, n});
          }
        }
    }
    bool pairSurvived = false;
    for (int x : possibleStarts[0])
      for (int y : possibleStarts[1])
        for (int z : possibleStarts[2]) {
          if (mixed && x < 7 && y < 7 && z < 7)
            continue;
          int c[] = {x, y, z};
          array<Mark *, 6> marks;
          for (int j = 0; j < 6; j++)
            marks[j] = &ports[j / 2][markedStart(c[j / 2], j % 2)];
          sort(marks.begin(), marks.end(), [](auto *p, auto *q) {
            return p->choices.size() < q->choices.size();
          });
          places[k]++;
          // Each prefix fixes separate left and right memberships in
          // matched-edge coordinates.
          auto dfs = [&](auto &&self, int j, Mask seenLeft, Mask seenRight,
                         Mask chosenLeft, Mask chosenRight) -> bool {
            if (j == 6) {
              completed[k]++;
              return true;
            }
            auto &p = *marks[j];
            for (auto [xx, yy] : p.choices) {
              if (((chosenLeft ^ xx) & seenLeft & p.l) ||
                  ((chosenRight ^ yy) & seenRight & p.r))
                continue;
              Mask u = chosenLeft | xx, v = chosenRight | yy,
                   L = seenLeft | p.l, R = seenRight | p.r;
              if ((u & v) || countBits(L & R & ~(u | v)) > missingLimit ||
                  countBits(u) > maximumLevel || countBits(v) > maximumLevel ||
                  33 - countBits(L & ~u) < minimumLevel ||
                  33 - countBits(R & ~v) < minimumLevel)
                continue;
              prefixes[k]++;
              if (self(self, j + 1, L, R, u, v))
                return true;
            }
            return false;
          };
          if (dfs(dfs, 0, 0, 0, 0, 0)) {
            finalLayouts[k]++;
            layouts << rr.first << ' ' << rr.second << ' ' << rr.motion << ' '
                    << k << ' ' << x << ' ' << y << ' ' << z << '\n';
            pairSurvived = true;
          }
        }
    if (pairSurvived)
      finalPairs[k]++;
  }
  if (in.gcount() || !in.eof())
    throw runtime_error("truncated pair file");
  layouts.close();
  if (!layouts)
    throw runtime_error("layout output error");
  for (int k = 0; k <= 33; k++)
    cout << k << " " << pairs[k] << " " << places[k] << " " << prefixes[k]
         << " " << finalPairs[k] << " " << finalLayouts[k] << endl;
}
