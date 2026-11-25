#pragma once
#include "atlas.hpp"
using Prefix = array<Mask, 3>;
vector<array<array<int, 7>, 3>> baseLayers;
vector<array<Mask, 392>> movedLayers;
vector<int> buckets, nextImage;
const int bucketCount = 1 << 23;
Mask mix(Mask x) {
  x ^= x >> 30;
  x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27;
  x *= 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}
int prefixBucket(const Prefix &q) {
  return (mix(q[0]) ^ (mix(q[1]) + 0xb4df96543ULL) * 7 ^
          (mix(q[2]) + 0x366847ULL) * 13) &
         (bucketCount - 1);
}
inline Mask layerMask(int b, const Descriptor &d, int h) {
  int y = mod(d.sign[0] * (h - d.shift[0]));
  return movedLayers[baseLayers[b][d.sourceAxis[0]][y]][d.plane[0]];
}
Prefix prefix(int b, int g) {
  const auto &d = motionAxes[g];
  return {layerMask(b, d, 0), layerMask(b, d, 1), layerMask(b, d, 2)};
}
// Index all ordered three-level prefixes; compare the entire prefix
// after a hash hit, retaining every orientation that realizes it.
void buildSingleLayers() {
  unordered_map<Mask, int> id;
  for (const auto &row : atlasSites) {
    array<array<int, 7>, 3> v;
    for (int a = 0; a < 3; a++)
      for (int t = 0; t < 7; t++) {
        Mask m = 0;
        for (int k : row) {
          int p[3] = {k / 49, k / 7 % 7, k % 7};
          if (p[a] == t) {
            int q = 0;
            for (int e = 0; e < 3; e++)
              if (e != a)
                q = q * 7 + p[e];
            m |= 1ull << q;
          }
        }
        auto it = id.find(m);
        if (it == id.end()) {
          int idx = id.size();
          it = id.emplace(m, idx).first;
          array<Mask, 392> row{};
          for (int g = 0; g < 392; g++)
            for (Mask z = m; z; z &= z - 1)
              row[g] |= 1ull << planarMotions[g][__builtin_ctzll(z)];
          movedLayers.push_back(row);
        }
        v[a][t] = it->second;
      }
    baseLayers.push_back(v);
  }
  // Exercise every signed permutation and translation against an explicit
  // set of 33 moved coordinates, including the reflected adjacent starts.
  for (int g = 0; g < int(motions.size()); ++g) {
    int b = g % atlasSites.size();
    array<array<Mask, 7>, 3> cuts{};
    Planes levels{};
    for (int site : atlasSites[b]) {
      int id = motions[g][site];
      array<int, 3> v{id / 49, id / 7 % 7, id % 7};
      levels[v[0]] |= Mask{1} << (id % 49);
      for (int a = 0; a < 3; ++a) {
        int q = 0;
        for (int d = 0; d < 3; ++d)
          if (a != d)
            q = 7 * q + v[d];
        for (int t : {v[a], mod(v[a] - 1)})
          cuts[a][t] |= Mask{1} << q;
      }
    }
    const auto indexedCuts = imageCuts(b, g);
    for (int t = 0; t < 7; ++t) {
      if (levels[t] != layerMask(b, motionAxes[g], t))
        throw runtime_error("moved level mismatch");
      for (int a = 0; a < 3; ++a)
        if (planar.at(cuts[a][t]) != indexedCuts[a][t])
          throw runtime_error("moved cut mismatch");
    }
  }
}
void indexFirstThreeLayers() {
  buildSingleLayers();
  buckets.assign(bucketCount, -1);
  nextImage.resize(atlasSites.size() * motions.size());
  for (int b = 0; b < (int)atlasSites.size(); b++)
    for (int g = 0; g < (int)motions.size(); g++) {
      int key = prefixBucket(prefix(b, g));
      int id = b * int(motions.size()) + g;
      nextImage[id] = buckets[key];
      buckets[key] = id;
    }
  cerr << "Prefix dictionary ready, 3D atlas covers " << nextImage.size()
       << " group images\n";
}
vector<Mask> planarMasks;
