// Check the two forced middles at overlap 16 directly in physical coordinates.
#include "middle_record.hpp"

using Band = array<Mask, 7>;
using Prefix = array<Mask, 3>;
int remainingPair(const array<int, 3> &v, int missing) {
  int code = 0;
  for (int d = 0; d < 3; ++d)
    if (d != missing)
      code = 7 * code + v[d];
  return code;
}

Mask contact(const Band &band, int localAxis, int start) {
  Mask projected = 0;
  for (int h = 0; h < 7; ++h)
    for (Mask m = band[h]; m; m &= m - 1) {
      int pos = __builtin_ctzll(m);
      int v[2] = {pos / 7, pos % 7};
      if (mod(v[localAxis] - start) < 2)
        projected |= Mask{1} << (7 * h + v[1 - localAxis]);
    }
  return projected;
}

struct Placement {
  int starts[6];
  array<Prefix, 6> required{};
  array<vector<Band>, 6> candidates;

  explicit Placement(const MiddleChoice &record) {
    for (int d = 0; d < 3; ++d) {
      starts[2 * d] = mod(record.centers[d] - 1);
      starts[2 * d + 1] = record.centers[d];
    }
    array<bool, 343> left{}, right{};
    for (int i : atlasSites[record.first])
      left[i] = true;
    for (int i : atlasSites[record.second])
      right[motions[record.motion][i]] = true;
    int intersection = 0;
    for (int i = 0; i < 343; ++i) {
      if (!left[i] && !right[i])
        continue;
      bool shared = left[i] && right[i];
      intersection += shared;
      int h = shared ? 1 : left[i] ? 0 : 2;
      array<int, 3> v{i / 49, i / 7 % 7, i % 7};
      for (int j = 0; j < 6; ++j) {
        int d = j / 2;
        if (mod(v[d] - starts[j]) < 2)
          required[j][h] |= Mask{1} << remainingPair(v, d);
      }
    }
    if (intersection != 16 || record.middleSize != 16)
      throw runtime_error("expected an entirely occupied 16-site intersection");
  }

  void add(const Band &band) {
    for (int j = 0; j < 6; ++j)
      if (equal(required[j].begin(), required[j].end(), band.begin()))
        candidates[j].push_back(band);
  }

  void verify() const {
    cout << "Pinned domains";
    for (const auto &d : candidates)
      cout << ' ' << d.size();
    cout << '\n';
    for (int j = 0; j < 6; ++j)
      for (int k = j + 1; k < 6; ++k) {
        int a = j / 2, b = k / 2;
        if (a == b)
          continue;
        bool compatible = false;
        for (const Band &x : candidates[j])
          for (const Band &y : candidates[k])
            if (contact(x, b - (b > a), starts[k]) ==
                contact(y, a - (a > b), starts[j]))
              compatible = true;
        if (!compatible) {
          cout << "Transverse pair with no common crossing " << j << ' ' << k
               << '\n';
          return;
        }
      }
    throw runtime_error("no transverse obstruction at overlap 16");
  }
};

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  readAtlas(argv[1]);
  ifstream input(argv[2], ios::binary);
  vector<Placement> tests;
  MiddleChoice row;
  while (input.read(reinterpret_cast<char *>(&row), sizeof(row)))
    if (row.intersectionSize == 16)
      tests.emplace_back(row);
  if (!input.eof() || input.gcount() || tests.size() != 2)
    return 1;
  vector<Image> images;
  for (int b = 0; b < int(atlasSites.size()); ++b) {
    distinctImages(b, images);
    for (const auto &image : images) {
      Band band{};
      for (int block = 0; block < 6; ++block) {
        for (Mask bits = image.bits[block]; bits; bits &= bits - 1) {
          int i = 64 * block + __builtin_ctzll(bits);
          band[i / 49] |= Mask{1} << (i % 49);
        }
      }
      for (auto &test : tests)
        test.add(band);
    }
  }
  for (const auto &test : tests)
    test.verify();
}
