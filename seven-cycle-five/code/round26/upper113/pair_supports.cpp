// Fix the first support up to isometry and enumerate every distinct
// labelled image of the second. Stabilizers are removed on the image itself.
#include "atlas.hpp"
int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  readAtlas(argv[1]);
  const int minOverlap = 16;
  int maxOverlap = stoi(argv[2]);
  ofstream f(argv[3], ios::binary);
  if (!f || maxOverlap < minOverlap || maxOverlap > 33)
    return 2;
  vector<Image> imgs;
  array<Mask, 34> total{};
  Mask labeled = 0;
  for (int b = 0; b < int(atlas.size()); b++) {
    distinctImages(b, imgs);
    labeled += imgs.size();
    array<Mask, 34> histogram{};
    for (int a = 0; a < (int)atlas.size(); a++) {
      const auto &s = representatives[a];
      for (const auto &im : imgs) {
        const auto &w = im.bits;
        int k = __builtin_popcountll(s[0] & w[0]) +
                __builtin_popcountll(s[1] & w[1]) +
                __builtin_popcountll(s[2] & w[2]) +
                __builtin_popcountll(s[3] & w[3]) +
                __builtin_popcountll(s[4] & w[4]) +
                __builtin_popcountll(s[5] & w[5]);
        if (k >= minOverlap && k <= maxOverlap) {
          histogram[k]++;
          array<uint16_t, 4> rec = {(uint16_t)a, (uint16_t)b, im.motion,
                                    (uint16_t)k};
          f.write((char *)rec.data(), sizeof(rec));
        }
      }
    }
    for (int k = minOverlap; k <= 33; k++)
      total[k] += histogram[k];
    cout << b << ' ' << imgs.size();
    for (int k = minOverlap; k <= 33; k++)
      cout << ' ' << histogram[k];
    cout << '\n' << flush;
  }
  f.close();
  if (!f || labeled != 16672544)
    return 1;
  cerr << "total labeled " << labeled << " histogram";
  for (int i = minOverlap; i <= 33; i++)
    cerr << ' ' << total[i];
  cerr << endl;
}
