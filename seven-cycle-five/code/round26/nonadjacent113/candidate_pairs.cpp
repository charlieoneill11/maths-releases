#include "gap_modes.hpp"
struct AtlasClasses {
  array<Mask, 16> b{};
};
int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  bool mixed = mixedMode(argv[2]);
  readAtlas(argv[1]);
  buildCutIndex();
  allowed.clear();
  int n = planar.size();
  vector<vector<int>> partners(n);
  for (auto &rw : baseCuts)
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++)
        for (int g = 0; g < 392; g++) {
          int l = movedCuts[rw[a][t]][g], r = movedCuts[rw[a][(t + 2) % 7]][g];
          partners[l].push_back(r);
          partners[r].push_back(l);
        }
  for (auto &v : partners) {
    sort(v.begin(), v.end());
    v.erase(unique(v.begin(), v.end()), v.end());
  }
  array<array<vector<AtlasClasses>, 7>, 3> compatibleFirst;
  for (auto &axis : compatibleFirst)
    for (auto &cut : axis)
      cut.resize(n);
  // Index all first supports simultaneously for each axis, mark and second
  // contact.
  for (int i = 0; i < 1016; i++) {
    auto c = imageCuts(i, 0);
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++)
        for (int v : partners[c[a][t]])
          compatibleFirst[a][t][v].b[i / 64] |= 1ull << (i % 64);
  }
  cerr << "bitset ready" << endl;
  ofstream out(argv[3], ios::binary);
  if (!out)
    throw runtime_error("cannot open pair output");
  uint64_t retained = 0, tested = 0;
  array<Mask, 34> hist{};

  for (int b = 0; b < 1016; b++) {
    vector<Image> ims;
    distinctImages(b, ims);
    for (auto &image : ims) {
      int g = image.motion;
      auto c = imageCuts(b, g);
      AtlasClasses candidates;
      AtlasClasses possible[3][2];
      for (int a = 0; a < 3; a++) {
        array<const AtlasClasses *, 7> p;
        for (int t = 0; t < 7; t++)
          p[t] = &compatibleFirst[a][t][c[a][t]];
        for (int k = 0; k < 1 + int(mixed); k++)
          for (int t = 0; t < 7; t++) {
            auto &x = p[t]->b;
            auto &y = p[(t + 2 + k) % 7]->b;
            for (int v = 0; v < 16; v++)
              possible[a][k].b[v] |= x[v] & y[v];
          }
      }
      for (int j = 0; j < 16; j++) {
        for (int m = mixed ? 1 : 0; m <= (mixed ? 7 : 0); m++) {
          Mask v = possible[0][m & 1].b[j] & possible[1][(m >> 1) & 1].b[j] &
                   possible[2][(m >> 2) & 1].b[j];
          candidates.b[j] |= v;
        }
      }
      tested += 1016;
      for (int j = 0; j < 16; j++)
        for (Mask m = candidates.b[j]; m; m &= m - 1) {
          int i = 64 * j + __builtin_ctzll(m);
          int k = 0;
          for (int v = 0; v < 6; v++)
            k += __builtin_popcountll(representatives[i][v] & image.bits[v]);
          SupportPair r{(uint16_t)i, (uint16_t)b, (uint16_t)g, (uint16_t)k};
          out.write((char *)&r, sizeof r);
          hist[k]++;
          retained++;
        }
    }
    if (b == 0 || (b + 1) % 50 == 0)
      cout << "b " << b << " total " << tested << " compatible " << retained
           << endl;
  }
  out.close();
  if (!out || tested != 16939304704ULL)
    throw runtime_error("incomplete normalized pair census");
  cout << "tested " << tested << " compatible " << retained << " hist";
  for (auto x : hist)
    cout << " " << x;
  cout << endl;
}
