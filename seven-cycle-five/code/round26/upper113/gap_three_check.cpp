// Independent recount of the distance-three search of Section 7.
//
// Usage: gap_three_check REPRESENTATIVES [--any-class] [FIRST END] [PAIRS.tsv]
//
// REPRESENTATIVES is atlas.tsv (seven plane masks per line) or classes33.txt
// (orbit size and 33 point indices per line). The program shares no code with
// gap_three.cpp or atlas.hpp. It lists every 33-code of Z_7^3 explicitly as a
// set of points, removes repeated images by comparing the sets, computes every
// cut directly from coordinates, and searches the pairs (S,T) of Lemma 18 with
// S = R_b + v. By default T and the six transverse projections are restricted
// to classes of index at least b, as in the paper; with --any-class there is
// no restriction on their classes, so the search does not depend on choosing
// the projection of least class index.
//
// For each class b of S the program prints the numbers of translates S with
// no T and with some T, and the number of distinct pairs (S,T); the optional
// PAIRS.tsv lists the distinct pairs by the classes of S and T. The recorded
// run (atlas.tsv, all classes, default restriction) took about 25 minutes on
// one core and 1.1 GB of memory. It printed 143566 and 204922 choices of S
// without and with a partner, 21378687 distinct pairs and no completion, in
// agreement class by class with gap_three.cpp. It exits with status 1 if it
// finds a completion.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using u64 = uint64_t;
using u32 = uint32_t;
using Point = array<int, 3>;
using Set343 = array<u64, 6>;

static int md(int x) { return ((x % 7) + 7) % 7; }
static bool confusable(const Point &x, const Point &y) {
  for (int k = 0; k < 3; k++) {
    int d = md(x[k] - y[k]);
    if (d > 1 && d < 6)
      return false;
  }
  return true;
}
static void fail(const string &m) { throw runtime_error(m); }

// Cut of a set at axis a and start 3*side, as a 49-bit planar mask in the
// two remaining coordinates, kept in their original order.
static array<u64, 6> cutsOf(const vector<Point> &pts) {
  array<u64, 6> c{};
  for (int a = 0; a < 3; a++)
    for (int side = 0; side < 2; side++)
      for (const Point &y : pts)
        if (md(y[a] - 3 * side) < 2) {
          int q = 0;
          for (int i = 0; i < 3; i++)
            if (i != a)
              q = 7 * q + y[i];
          u64 bit = u64(1) << q;
          if (c[2 * a + side] & bit)
            fail("a cut of a code is not injective");
          c[2 * a + side] |= bit;
        }
  return c;
}

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  bool anyClass = false;
  vector<string> rest;
  for (int i = 2; i < argc; i++) {
    string s = argv[i];
    if (s == "--any-class")
      anyClass = true;
    else
      rest.push_back(s);
  }
  int first = 0, end = 1016;
  string pairsPath;
  if (rest.size() >= 2) {
    first = stoi(rest[0]);
    end = stoi(rest[1]);
  }
  if (rest.size() == 1 || rest.size() == 3)
    pairsPath = rest.back();

  // Representatives.
  vector<vector<Point>> reps;
  vector<long long> recordedOrbit;
  {
    ifstream in(argv[1]);
    if (!in)
      fail("cannot open representatives");
    string line;
    while (getline(in, line)) {
      istringstream f(line);
      vector<long long> v;
      long long x;
      while (f >> x)
        v.push_back(x);
      vector<Point> pts;
      if (v.size() == 7) {
        for (int u = 0; u < 7; u++)
          for (int bit = 0; bit < 49; bit++)
            if (v[u] >> bit & 1)
              pts.push_back({u, bit / 7, bit % 7});
        recordedOrbit.push_back(-1);
      } else if (v.size() == 34) {
        for (int i = 1; i < 34; i++)
          pts.push_back({int(v[i] / 49), int(v[i] / 7 % 7), int(v[i] % 7)});
        recordedOrbit.push_back(v[0]);
      } else
        fail("malformed representative line");
      if (pts.size() != 33)
        fail("representative without 33 words");
      for (size_t i = 0; i < pts.size(); i++)
        for (size_t j = i + 1; j < pts.size(); j++)
          if (pts[i] == pts[j] || confusable(pts[i], pts[j]))
            fail("representative is not a code");
      reps.push_back(pts);
    }
  }
  if (reps.size() != 1016)
    fail("expected 1016 representatives");
  if (first < 0 || first > end || end > 1016)
    return 2;

  // All images under G_3: y_k = +-x_{p(k)} + t_k.
  vector<array<int, 3>> perms;
  {
    array<int, 3> p{0, 1, 2};
    do
      perms.push_back(p);
    while (next_permutation(p.begin(), p.end()));
  }
  unordered_map<u64, u32> maskId;
  maskId.reserve(1 << 18);
  auto idOf = [&](u64 m) {
    auto it = maskId.emplace(m, u32(maskId.size())).first;
    return it->second;
  };
  vector<array<u32, 6>> cut;
  vector<uint16_t> cls;
  vector<pair<u64, u64>> fingerprints;
  vector<int> stab(1016);
  cut.reserve(16672544);
  cls.reserve(16672544);
  fingerprints.reserve(16672544);
  map<int, int> stabHistogram;
  for (int b = 0; b < 1016; b++) {
    vector<Set343> images;
    images.reserve(16464);
    for (auto &p : perms)
      for (int sg = 0; sg < 8; sg++)
        for (int t = 0; t < 343; t++) {
          int tr[3] = {t / 49, t / 7 % 7, t % 7};
          Set343 s{};
          for (const Point &x : reps[b]) {
            int y[3];
            for (int k = 0; k < 3; k++)
              y[k] = md(((sg >> k) & 1 ? -x[p[k]] : x[p[k]]) + tr[k]);
            int i = 49 * y[0] + 7 * y[1] + y[2];
            s[i / 64] |= u64(1) << (i % 64);
          }
          images.push_back(s);
        }
    if (images.size() != 16464)
      fail("wrong group order");
    sort(images.begin(), images.end());
    images.erase(unique(images.begin(), images.end()), images.end());
    if (16464 % images.size())
      fail("orbit size does not divide 16464");
    stab[b] = 16464 / images.size();
    stabHistogram[stab[b]]++;
    if (recordedOrbit[b] >= 0 && recordedOrbit[b] != (long long)images.size())
      fail("recorded orbit size differs");
    for (const Set343 &s : images) {
      vector<Point> pts;
      u64 h1 = 0x9e3779b97f4a7c15ull, h2 = 0xc2b2ae3d27d4eb4full;
      for (int w = 0; w < 6; w++) {
        h1 = (h1 ^ s[w]) * 0xff51afd7ed558ccdull;
        h1 ^= h1 >> 33;
        h2 = (h2 + s[w]) * 0x94d049bb133111ebull;
        h2 ^= h2 >> 31;
        for (u64 m = s[w]; m; m &= m - 1) {
          int i = 64 * w + __builtin_ctzll(m);
          pts.push_back({i / 49, i / 7 % 7, i % 7});
        }
      }
      if (pts.size() != 33)
        fail("image without 33 words");
      auto c = cutsOf(pts);
      array<u32, 6> ids;
      for (int j = 0; j < 6; j++)
        ids[j] = idOf(c[j]);
      cut.push_back(ids);
      cls.push_back(uint16_t(b));
      fingerprints.emplace_back(h1, h2);
    }
  }
  const size_t N = cut.size();
  sort(fingerprints.begin(), fingerprints.end());
  if (adjacent_find(fingerprints.begin(), fingerprints.end()) != fingerprints.end())
    fail("two classes share a code");
  vector<pair<u64, u64>>().swap(fingerprints);
  const u32 M = maskId.size();
  cout << "codes " << N << " planar masks " << M << " stabilisers";
  for (auto [s, n] : stabHistogram)
    cout << " " << s << ":" << n;
  cout << "\nclasses with nontrivial stabiliser:";
  for (int b = 0; b < 1016; b++)
    if (stab[b] > 1)
      cout << " " << b << ":" << stab[b];
  cout << endl;
  if (N != 16672544)
    fail("expected 16672544 codes");

  // The relation P_3 from all three axes of all codes, closed under reversal.
  vector<u64> rel;
  rel.reserve(6 * N);
  for (size_t j = 0; j < N; j++)
    for (int a = 0; a < 3; a++)
      rel.push_back(u64(cut[j][2 * a]) << 32 | cut[j][2 * a + 1]);
  sort(rel.begin(), rel.end());
  rel.erase(unique(rel.begin(), rel.end()), rel.end());
  size_t forward = rel.size();
  for (size_t i = 0; i < forward; i++)
    rel.push_back(rel[i] << 32 | rel[i] >> 32);
  sort(rel.begin(), rel.end());
  rel.erase(unique(rel.begin(), rel.end()), rel.end());
  cout << "ordered pairs in P3 " << rel.size() << " (closed under reversal: "
       << (rel.size() == forward ? "yes" : "no") << ")" << endl;
  vector<u32> pOff(M + 1), pList(rel.size());
  for (size_t i = 0; i < rel.size(); i++) {
    pOff[(rel[i] >> 32) + 1]++;
    pList[i] = u32(rel[i]);
  }
  for (u32 m = 0; m < M; m++)
    pOff[m + 1] += pOff[m];
  vector<u64>().swap(rel);
  auto inP = [&](u32 m, u32 x) {
    return binary_search(pList.begin() + pOff[m], pList.begin() + pOff[m + 1], x);
  };

  // For each axis a, the codes grouped by their two cuts on that axis.
  struct Index {
    vector<u64> keys;          // distinct (first cut, second cut), sorted
    vector<u32> off, ids;      // codes of keys[k] are ids[off[k]..off[k+1])
    vector<u32> firstStart;    // keys with first cut m are firstStart[m..m+1)
  };
  array<Index, 3> index;
  for (int a = 0; a < 3; a++) {
    vector<pair<u64, u32>> e(N);
    for (size_t j = 0; j < N; j++)
      e[j] = {u64(cut[j][2 * a]) << 32 | cut[j][2 * a + 1], u32(j)};
    sort(e.begin(), e.end());
    auto &I = index[a];
    I.ids.resize(N);
    for (size_t j = 0; j < N; j++) {
      if (j == 0 || e[j].first != e[j - 1].first) {
        I.keys.push_back(e[j].first);
        I.off.push_back(j);
      }
      I.ids[j] = e[j].second;
    }
    I.off.push_back(N);
    I.firstStart.assign(M + 1, 0);
    for (u64 key : I.keys)
      I.firstStart[(key >> 32) + 1]++;
    for (u32 m = 0; m < M; m++)
      I.firstStart[m + 1] += I.firstStart[m];
  }
  auto range = [&](int a, u64 key) -> pair<u32, u32> {
    auto &I = index[a];
    auto lo = I.keys.begin() + I.firstStart[key >> 32],
         hi = I.keys.begin() + I.firstStart[(key >> 32) + 1];
    auto it = lower_bound(lo, hi, key);
    if (it == hi || *it != key)
      return {0, 0};
    size_t k = it - I.keys.begin();
    return {I.off[k], I.off[k + 1]};
  };

  ofstream pairsOut;
  if (!pairsPath.empty())
    pairsOut.open(pairsPath);
  unsigned long long totalPairs = 0, totalEmpty = 0, totalNonempty = 0,
                     completions = 0, roots = 0;
  vector<unsigned long long> pairsByClass(1016);
  for (int b = first; b < end; b++) {
    unsigned long long empty = 0, nonempty = 0, pairs = 0;
    fill(pairsByClass.begin(), pairsByClass.end(), 0);
    for (int v = 0; v < 343; v++) {
      roots++;
      int sh[3] = {v / 49, v / 7 % 7, v % 7};
      vector<Point> pts;
      for (const Point &x : reps[b])
        pts.push_back({md(x[0] + sh[0]), md(x[1] + sh[1]), md(x[2] + sh[2])});
      auto c = cutsOf(pts);
      array<u32, 6> S;
      for (int j = 0; j < 6; j++) {
        auto it = maskId.find(c[j]);
        if (it == maskId.end())
          fail("cut of S missing from the table");
        S[j] = it->second;
      }
      int best = 0;
      u64 bestCost = ~u64(0);
      for (int a = 0; a < 3; a++) {
        u64 cost = u64(pOff[S[2 * a] + 1] - pOff[S[2 * a]]) *
                   (pOff[S[2 * a + 1] + 1] - pOff[S[2 * a + 1]]);
        if (cost < bestCost) {
          bestCost = cost;
          best = a;
        }
      }
      unsigned long long here = 0;
      // Keys (x, y) on axis best with x a partner of S's first cut and y a
      // partner of its second cut: merge each block of x with the partners.
      vector<u32> matchedKeys;
      {
        auto &I = index[best];
        u32 yb = pOff[S[2 * best + 1]], ye = pOff[S[2 * best + 1] + 1];
        for (u32 i = pOff[S[2 * best]]; i < pOff[S[2 * best] + 1]; i++) {
          u32 x = pList[i], k = I.firstStart[x], ke = I.firstStart[x + 1], j = yb;
          while (k < ke && j < ye) {
            u32 y = u32(I.keys[k]);
            if (y < pList[j])
              k++;
            else if (pList[j] < y)
              j++;
            else {
              matchedKeys.push_back(k);
              k++;
              j++;
            }
          }
        }
      }
      for (u32 mk : matchedKeys) {
          u32 lo = index[best].off[mk], hi = index[best].off[mk + 1];
          for (u32 q = lo; q < hi; q++) {
            u32 T = index[best].ids[q];
            if (!anyClass && cls[T] < b)
              continue;
            bool ok = true;
            for (int a = 0; a < 3 && ok; a++)
              if (a != best)
                ok = inP(S[2 * a], cut[T][2 * a]) &&
                     inP(S[2 * a + 1], cut[T][2 * a + 1]);
            if (!ok)
              continue;
            here++;
            pairsByClass[cls[T]]++;
            // Six transverse projections W with the prescribed cuts at
            // starts 0 and 3 on their first axis.
            array<vector<u32>, 6> dom;
            bool emptyDomain = false;
            for (int j = 0; j < 6 && !emptyDomain; j++) {
              auto [l2, h2] = range(0, u64(S[j]) << 32 | cut[T][j]);
              for (u32 r = l2; r < h2; r++) {
                u32 W = index[0].ids[r];
                if (anyClass || cls[W] >= b)
                  dom[j].push_back(W);
              }
              emptyDomain = dom[j].empty();
            }
            if (emptyDomain)
              continue;
            array<int, 6> order{0, 1, 2, 3, 4, 5};
            sort(order.begin(), order.end(),
                 [&](int x, int y) { return dom[x].size() < dom[y].size(); });
            array<u32, 6> chosen{};
            // Band j lies on axis j/2 of S (axis j/2+1 of the four-dimensional
            // frame) at start 3*(j%2). Its projection keeps the first axis as
            // its axis 0, and the other transverse axis a' becomes its axis
            // 1 + a' - (a' > a).
            auto slot = [](int j, int k) {
              int a = j / 2, a2 = k / 2;
              return 2 * (1 + a2 - (a2 > a)) + k % 2;
            };
            auto search = [&](auto &&self, int t) -> bool {
              if (t == 6)
                return true;
              int j = order[t];
              for (u32 W : dom[j]) {
                bool fits = true;
                for (int u = 0; u < t && fits; u++) {
                  int k = order[u];
                  if (k / 2 != j / 2 &&
                      cut[W][slot(j, k)] != cut[chosen[k]][slot(k, j)])
                    fits = false;
                }
                if (fits) {
                  chosen[j] = W;
                  if (self(self, t + 1))
                    return true;
                }
              }
              return false;
            };
            if (search(search, 0)) {
              completions++;
              cout << "completion class " << b << " shift " << v << " T " << T
                   << endl;
            }
          }
        }
      pairs += here;
      (here ? nonempty : empty)++;
    }
    totalPairs += pairs;
    totalEmpty += empty;
    totalNonempty += nonempty;
    cout << "class " << b << " empty " << empty << " nonempty " << nonempty
         << " pairs " << pairs << " cumulative " << totalPairs
         << " completions " << completions << endl;
    if (pairsOut)
      for (int c = 0; c < 1016; c++)
        if (pairsByClass[c])
          pairsOut << b << '\t' << c << '\t' << pairsByClass[c] << '\n';
  }
  cout << "Summary: " << roots << " choices of S, " << totalEmpty
       << " with no T, " << totalNonempty << " with some T, " << totalPairs
       << " distinct pairs (S,T), " << completions
       << " admitting six projections with agreeing crossings"
       << (anyClass ? " (classes unrestricted)" : "") << endl;
  return completions != 0;
}
