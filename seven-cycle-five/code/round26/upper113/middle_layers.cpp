#include "middle_record.hpp"
#include "prefixes.hpp"

using Pair = std::pair<Mask, Mask>;
vector<Pair> possibleMiddles;
unordered_map<Mask, pair<int, int>> ranges;
// For each ordered pair of projected adjacent cuts, recover every possible
// middle-layer planar mask, including the reversal of the height axis.
void indexMiddleCuts() {
  possibleMiddles.reserve(2 * 1016 * 3 * 7 * 392);
  for (int b = 0; b < 1016; b++)
    for (int d = 0; d < 3; d++)
      for (int t = 0; t < 7; t++)
        for (int h = 0; h < 392; h++) {
          int t1 = (t + 1) % 7;
          Mask l = movedCuts[baseCuts[b][d][t]][h],
               r = movedCuts[baseCuts[b][d][t1]][h];
          Mask m = movedLayers[baseLayers[b][d][t1]][h];
          possibleMiddles.emplace_back((l << 32) | r, m);
          possibleMiddles.emplace_back((r << 32) | l, m);
        }
  sort(possibleMiddles.begin(), possibleMiddles.end());
  possibleMiddles.erase(unique(possibleMiddles.begin(), possibleMiddles.end()),
                        possibleMiddles.end());
  ranges.reserve(allowed.size());
  for (int i = 0, j; i < (int)possibleMiddles.size(); i = j) {
    for (j = i + 1; j < (int)possibleMiddles.size() &&
                    possibleMiddles[j].first == possibleMiddles[i].first;
         j++)
      ;
    ranges[possibleMiddles[i].first] = {i, j};
  }
  assert(ranges.size() == allowed.size());
  for (const auto &row : atlasSites) {
    AxisCuts p{};
    for (int n = 0; n < 33; n++) {
      int k = row[n], v[3] = {k / 49, k / 7 % 7, k % 7};
      for (int a = 0; a < 3; a++) {
        int q = 0;
        for (int e = 0; e < 3; e++)
          if (a != e)
            q = q * 7 + v[e];
        for (int t : {v[a], mod(v[a] - 1)}) {
          Mask bit = 1ull << n;
          assert(p[a][t].pointBit[q] == 0);
          p[a][t].pointBit[q] = bit;
          p[a][t].cover |= bit;
        }
      }
    }
    ports.push_back(p);
  }
  cerr << "distinct marked prefixes " << possibleMiddles.size()
       << ", ordered contact pairs " << ranges.size() << '\n';
}
int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  readAtlas(argv[1]);
  buildCutIndex();
  buildSingleLayers();
  indexMiddleCuts();
  vector<Cuts> ref;
  for (int i = 0; i < 1016; i++)
    ref.push_back(imageCuts(i, 0));
  ifstream input(argv[2], ios::binary);
  ofstream output(argv[3], ios::binary);
  CenteredPair r;
  array<Mask, 34> tested{}, pairs{}, layouts{}, products{};
  int prev = -1;
  vector<SupportBits> variant(16464);
  vector<Cuts> cuts(16464);

  while (input.read((char *)&r, sizeof(r))) {
    tested[r.intersectionSize]++;
    const auto gaps = transverseDistances(r.distanceCode);
    if (prev != r.second) {
      for (int g = 0; g < 16464; g++) {
        auto &v = variant[g];
        v = {};
        for (int i : atlasSites[r.second]) {
          int j = motions[g][i];
          v[j / 64] |= 1ull << (j % 64);
        }
        cuts[g] = imageCuts(r.second, g);
      }
      prev = r.second;
    }
    Mask intersection = 0;
    for (int i = 0; i < 33; i++) {
      int q = atlasSites[r.first][i];
      if (variant[r.motion][q / 64] >> (q % 64) & 1)
        intersection |= 1ull << i;
    }
    assert(__builtin_popcountll(intersection) == r.intersectionSize);
    // Each transverse cut prescribes both the selected and the absent bits
    // of the physical middle on the part of the intersection inside that cut.
    array<array<Assignment, 7>, 3> centered;
    bool has = true;
    for (int a = 0; a < 3 && has; a++) {
      int centers = r.centers[a], gap = gaps[a],
          needed =
              centers | (((centers >> gap) | (centers << (7 - gap))) & 127);
      array<Assignment, 7> singles;
      for (int t = 0; t < 7; t++)
        if (needed >> t & 1) {
          const auto &p = ports[r.first][a][t];
          singles[t].bits = intersection & p.cover;
          Mask key = (Mask(ref[r.first][a][t]) << 32) | cuts[r.motion][a][t];
          auto [left, right] = ranges.at(key);
          for (int j = left; j < right; j++) {
            Mask us = 0;
            for (Mask b = possibleMiddles[j].second; b; b &= b - 1)
              us |= p.pointBit[__builtin_ctzll(b)];
            if (!(us & ~intersection))
              singles[t].selected.push_back(us);
          }
        }
      bool any = false;
      for (int c = 0; c < 7; c++)
        if (centers >> c & 1) {
          auto &l = singles[mod(c - gap)], &h = singles[c],
               &dest = centered[a][c];
          dest.bits = l.bits | h.bits;
          Mask both = l.bits & h.bits;
          for (Mask u : l.selected)
            for (Mask v : h.selected)
              if (!((u ^ v) & both)) {
                Mask selected = u | v;
                if (__builtin_popcountll(selected) <= 19 &&
                    __builtin_popcountll(selected |
                                         (intersection ^ dest.bits)) >= 16)
                  dest.selected.push_back(selected);
              }
          if (!dest.selected.empty()) {
            sort(dest.selected.begin(), dest.selected.end());
            dest.selected.erase(
                unique(dest.selected.begin(), dest.selected.end()),
                dest.selected.end());
            any = true;
          }
        }
      has = any;
    }
    if (!has)
      continue;
    bool got = false;
    // Agree on every shared bit before enumerating the uncovered sites.
    for (int b = 0; b < 7; b++)
      for (int c = 0; c < 7; c++)
        for (int d = 0; d < 7; d++) {
          const Assignment &x = centered[0][b], &y = centered[1][c],
                           &z = centered[2][d];
          if (x.selected.empty() || y.selected.empty() || z.selected.empty())
            continue;
          Mask sharedXY = x.bits & y.bits,
               sharedXYZ = (x.bits | y.bits) & z.bits,
               free = intersection & ~(x.bits | y.bits | z.bits);
          bool placed = false;
          for (Mask u : x.selected)
            for (Mask v : y.selected)
              if (!((u ^ v) & sharedXY))
                for (Mask w : z.selected)
                  if (!(((u | v) ^ w) & sharedXYZ)) {
                    Mask fixed = u | v | w;
                    for (Mask opt = free;; opt = (opt - 1) & free) {
                      Mask middle = fixed | opt;
                      int n = __builtin_popcountll(middle);
                      if (n >= 16 && n <= 19) {
                        MiddleChoice j{middle,
                                       r.first,
                                       r.second,
                                       r.motion,
                                       r.intersectionSize,
                                       {uint8_t(b), uint8_t(c), uint8_t(d)},
                                       uint8_t(n),
                                       r.distanceCode};
                        output.write((char *)&j, sizeof(j));
                        products[r.intersectionSize]++;
                        placed = true;
                      }
                      if (!opt)
                        break;
                    }
                  }
          if (placed) {
            got = true;
            layouts[r.intersectionSize]++;
          }
        }
    if (got)
      pairs[r.intersectionSize]++;
  }
  output.close();
  if (!input.eof() || input.gcount() || !output)
    throw runtime_error("binary record input or output failed");
  cout << "intersection\ttested\tpairs\tplaces\tmiddles\n";
  for (int k = 16; k <= 33; k++)
    cout << k << '\t' << tested[k] << '\t' << pairs[k] << '\t' << layouts[k]
         << '\t' << products[k] << '\n';
}
