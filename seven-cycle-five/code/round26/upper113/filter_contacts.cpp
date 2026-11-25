// Require two transverse full bands at each specified distance.
#include "atlas.hpp"
int main(int argc, char **argv) {
  if (argc != 4 && argc != 5)
    return 2;
  const auto orders = distanceOrders(argc == 5 ? argv[4] : "111");
  readAtlas(argv[1]);
  buildCutIndex();
  vector<Cuts> ref;
  for (int i = 0; i < 1016; i++)
    ref.push_back(imageCuts(i, 0));
  ifstream in(argv[2], ios::binary);
  ofstream out(argv[3], ios::binary);
  int prev = -1;
  vector<Cuts> variants(motions.size());
  SupportPair r;
  array<Mask, 34> tested{}, alive{};
  Mask placed = 0;
  while (in.read((char *)&r, sizeof r)) {
    if (r.second != prev) {
      for (int g = 0; g < (int)motions.size(); g++)
        variants[g] = imageCuts(r.second, g);
      prev = r.second;
    }
    auto &S = ref[r.first];
    auto &T = variants[r.motion];
    CenteredPair k{r.first, r.second, r.motion, r.intersectionSize, {}, 0};
    tested[r.intersectionSize]++;
    array<int, 3> validStarts{};
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++)
        if (allowed.count((Mask(S[a][t]) << 32) | T[a][t]))
          validStarts[a] |= 1 << t;
    // Normalizing the first support may permute the transverse axes.
    for (unsigned code : orders) {
      k.distanceCode = uint8_t(code);
      const auto gaps = transverseDistances(code);
      int combinations = 1;
      for (int a = 0; a < 3; a++) {
        int mask = validStarts[a], gap = gaps[a];
        int later = ((mask << gap) | (mask >> (7 - gap))) & 127;
        k.centers[a] = mask & later;
        combinations *= __builtin_popcount(k.centers[a]);
      }
      if (combinations) {
        out.write((char *)&k, sizeof k);
        alive[r.intersectionSize]++;
        placed += combinations;
      }
    }
  }
  out.close();
  if (!in.eof() || in.gcount() || !out)
    throw runtime_error("binary record input or output failed");
  cout << "intersection\ttested\ttransverse\n";
  for (int k = 16; k <= 33; k++)
    cout << k << '\t' << tested[k] << '\t' << alive[k] << '\n';
  cout << "centered choices " << placed << endl;
}
