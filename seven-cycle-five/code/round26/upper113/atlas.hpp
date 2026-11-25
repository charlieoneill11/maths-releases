#pragma once
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
using Mask = uint64_t;
using SupportBits = array<Mask, 6>;
using Sites = array<int, 33>;
using Motion = array<int16_t, 343>;
using Planes = array<Mask, 7>;
vector<Motion> motions;
vector<SupportBits> representatives;
vector<Sites> atlasSites;
vector<Planes> atlas;
void readAtlas(const char *file) {
  std::ifstream input(file);
  if (!input)
    throw std::runtime_error("cannot open 33-set atlas");
  std::string line;
  while (std::getline(input, line)) {
    std::istringstream fields(line);
    Planes planes{};
    Sites row{};
    SupportBits bits{};
    int count = 0;
    for (auto &plane : planes)
      if (!(fields >> plane) || (plane >> 49))
        throw std::runtime_error("invalid atlas plane");
    std::string extra;
    if (fields >> extra)
      throw std::runtime_error("extra atlas field");
    for (int site = 0; site < 343; site++)
      if ((planes[site / 49] >> (site % 49)) & 1) {
        if (count >= 33)
          throw std::runtime_error("oversized atlas row");
        row[count++] = site;
        bits[site / 64] |= Mask(1) << (site % 64);
      }
    if (count != 33)
      throw std::runtime_error("incorrect atlas row size");
    representatives.push_back(bits);
    atlas.push_back(planes);
    atlasSites.push_back(row);
  }
  if (!input.eof() || atlas.size() != 1016)
    throw std::runtime_error("incomplete atlas");
  array<int, 3> p = {0, 1, 2};
  do {
    for (int flips = 0; flips < 8; flips++)
      for (int t = 0; t < 343; t++) {
        Motion m;
        for (int i = 0; i < 343; i++) {
          int q[3] = {i / 49, i / 7 % 7, i % 7},
              v[3] = {t / 49, t / 7 % 7, t % 7};
          int k = 0;
          for (int d = 0; d < 3; d++)
            k = 7 * k +
                (v[d] + ((flips >> d & 1) ? -q[p[d]] : q[p[d]]) + 7) % 7;
          m[i] = k;
        }
        motions.push_back(m);
      }
  } while (next_permutation(p.begin(), p.end()));
  assert(motions.size() == 16464);
}
struct Image {
  SupportBits bits;
  uint16_t motion;
};
void distinctImages(int b, vector<Image> &v) {
  v.clear();
  int j = 0;
  for (const auto &m : motions) {
    SupportBits im{};
    for (int i : atlasSites[b]) {
      int k = m[i];
      im[k / 64] |= 1ull << (k % 64);
    }
    v.push_back({im, (uint16_t)j++});
  }
  sort(v.begin(), v.end(), [](const auto &a, const auto &b) {
    return a.bits != b.bits ? a.bits < b.bits : a.motion < b.motion;
  });
  v.erase(unique(v.begin(), v.end(),
                 [](const auto &a, const auto &b) { return a.bits == b.bits; }),
          v.end());
}

using MaskId = uint32_t;
struct SupportPair {
  uint16_t first, second, motion, intersectionSize;
};
struct CenteredPair {
  uint16_t first, second, motion, intersectionSize;
  uint8_t centers[3], distanceCode;
};
static_assert(sizeof(SupportPair) == 8 && sizeof(CenteredPair) == 12);
using Distances = array<int, 3>;

// Encoding 0 represents the original three adjacent transverse pairs.
Distances transverseDistances(unsigned code) {
  if (code >= 27)
    throw runtime_error("invalid transverse distance code");
  return {int(code / 9 + 1), int(code / 3 % 3 + 1), int(code % 3 + 1)};
}

vector<unsigned> distanceOrders(const string &profile) {
  if (profile.size() != 3 || profile.find_first_not_of("123") != string::npos)
    throw runtime_error("expected three transverse distances in 1,2,3");
  string order = profile;
  sort(order.begin(), order.end());
  vector<unsigned> codes;
  do {
    unsigned code = 0;
    for (char digit : order)
      code = 3 * code + unsigned(digit - '1');
    codes.push_back(code);
  } while (next_permutation(order.begin(), order.end()));
  return codes;
}

vector<vector<MaskId>> movedCuts;
unordered_map<Mask, MaskId> planar;
using Cuts = array<array<MaskId, 7>, 3>;
vector<Cuts> baseCuts;
array<array<int, 49>, 392> planarMotions;
struct Descriptor {
  array<int, 3> sourceAxis, plane, shift, sign;
};
vector<Descriptor> motionAxes;
unordered_set<Mask> allowed;
int mod(int v) { return (v + 21) % 7; }
// Index every projected two-level cut of a 33-set. Encode a physical
// planar mask by an integer only after applying its planar isometry.
void buildCutIndex() {
  int j = 0;
  for (int swap = 0; swap < 2; swap++)
    for (int sy : {1, -1})
      for (int sx : {1, -1})
        for (int y = 0; y < 7; y++)
          for (int x = 0; x < 7; x++) {
            for (int k = 0; k < 49; k++) {
              int q[2] = {k / 7, k % 7};
              planarMotions[j][k] =
                  7 * mod(sy * q[swap] + y) + mod(sx * q[1 - swap] + x);
            }
            j++;
          }
  array<int, 3> perm = {0, 1, 2};
  do {
    for (int f = 0; f < 8; f++)
      for (int t = 0; t < 343; t++) {
        Descriptor d;
        int shift[3] = {t / 49, t / 7 % 7, t % 7};
        for (int a = 0; a < 3; a++) {
          int y = (a == 0 ? 1 : 0), x = (a == 2 ? 1 : 2);
          int flipY = (f >> y) & 1, flipX = (f >> x) & 1;
          d.sourceAxis[a] = perm[a];
          d.shift[a] = shift[a];
          d.sign[a] = (f >> a & 1) ? -1 : 1;
          d.plane[a] = (((int(perm[y] > perm[x]) * 2 + flipY) * 2 + flipX) * 7 +
                        shift[y]) *
                           7 +
                       shift[x];
        }
        motionAxes.push_back(d);
      }
  } while (next_permutation(perm.begin(), perm.end()));
  unordered_map<Mask, MaskId> basis;
  for (auto &row : atlasSites) {
    Cuts c{};
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++) {
        Mask bits = 0;
        for (int pt : row) {
          int p[3] = {pt / 49, pt / 7 % 7, pt % 7};
          if (mod(p[a] - t) < 2) {
            int id = 0;
            for (int i = 0; i < 3; i++)
              if (i != a)
                id = 7 * id + p[i];
            bits |= 1ull << id;
          }
        }
        auto it = basis.find(bits);
        if (it == basis.end()) {
          MaskId idx = movedCuts.size();
          it = basis.emplace(bits, idx).first;
          movedCuts.emplace_back();
          for (int h = 0; h < 392; h++) {
            Mask u = 0;
            for (Mask s = bits; s; s &= s - 1)
              u |= 1ull << planarMotions[h][__builtin_ctzll(s)];
            auto entry = planar.emplace(u, planar.size());
            movedCuts.back().push_back(entry.first->second);
          }
        }
        c[a][t] = it->second;
      }
    baseCuts.push_back(c);
  }
  for (const auto &c : baseCuts)
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++)
        for (int h = 0; h < 392; h++) {
          Mask l = movedCuts[c[a][t]][h], r = movedCuts[c[a][(t + 1) % 7]][h];
          allowed.insert((l << 32) | r);
          allowed.insert((r << 32) | l);
        }
  cerr << "basis " << basis.size() << " planar " << planar.size() << " allowed "
       << allowed.size() << "\n";
}
// Pull each target cut start planarMasks through the height reflection or
// shift. A negative sign sends {t,t+1} to a reversed pair starting layerMask
// level earlier.
Cuts imageCuts(int b, int g) {
  Cuts v{};
  const auto &p = motionAxes[g];
  for (int a = 0; a < 3; a++)
    for (int t = 0; t < 7; t++) {
      int s = p.sign[a], u = mod(s * (t - p.shift[a]) - (s < 0));
      v[a][t] = movedCuts[baseCuts[b][p.sourceAxis[a]][u]][p.plane[a]];
    }
  return v;
}
