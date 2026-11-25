// Complete the nonadjacent projected marks against a fixed union of adjacent
// slabs.
#include "prefixes.hpp"
#include <bitset>
#include <set>

using Point = array<int, 4>;
using Space = bitset<2401>;
struct Mark {
  int axis, start;
};
struct Candidate {
  Planes planes{};
  array<array<Mask, 7>, 3> cuts{};
};

int siteId(const Point &p) { return ((7 * p[0] + p[1]) * 7 + p[2]) * 7 + p[3]; }
Point coordinates(int id) {
  return {id / 343, id / 49 % 7, id / 7 % 7, id % 7};
}
int otherAxis(int a, int b) { return b - int(b > a); }

vector<Candidate> candidates(const Mark &mark, int adjacentAxes,
                             const vector<Point> &fixed,
                             const Space &available) {
  Planes seen{}, known{};
  for (const Point &p : fixed) {
    if (mod(p[mark.axis] - mark.start) >= 2)
      continue;
    int i = 0;
    for (int a = 0; a < 4; a++)
      if (a != mark.axis)
        i = 7 * i + p[a];
    seen[i / 49] |= Mask(1) << (i % 49);
  }
  for (int i = 0; i < 343; i++) {
    array<int, 3> p{i / 49, i / 7 % 7, i % 7};
    for (int a = 0; a < adjacentAxes; a++)
      if (p[a] == 6 || p[a] < 2)
        known[i / 49] |= Mask(1) << (i % 49);
  }
  Prefix target{seen[6], seen[0], seen[1]};
  set<Planes> distinct;
  vector<Candidate> result;
  for (int id = buckets[prefixBucket(target)]; id >= 0; id = nextImage[id]) {
    int b = id / 16464, motion = id % 16464;
    if (prefix(b, motion) != target)
      continue;
    Candidate candidate;
    bool agrees = true;
    for (int h = 0; h < 7; h++) {
      candidate.planes[h] = layerMask(b, motionAxes[motion], (h + 1) % 7);
      if ((candidate.planes[h] & known[h]) != seen[h])
        agrees = false;
    }
    if (!agrees || !distinct.insert(candidate.planes).second)
      continue;
    for (int h = 0; h < 7 && agrees; h++)
      for (Mask bits = candidate.planes[h]; bits; bits &= bits - 1) {
        int i = __builtin_ctzll(bits);
        array<int, 3> q{h, i / 7, i % 7};
        if (!(known[h] >> i & 1)) {
          Point p{};
          int j = 0;
          for (int a = 0; a < 4; a++)
            if (a != mark.axis)
              p[a] = q[j++];
          p[mark.axis] = mark.start;
          bool canLift = available[siteId(p)];
          p[mark.axis] = (mark.start + 1) % 7;
          if (!canLift && !available[siteId(p)]) {
            agrees = false;
            break;
          }
        }
        for (int d = 0; d < 3; d++) {
          int suffix = 0;
          for (int a = 0; a < 3; a++)
            if (a != d)
              suffix = 7 * suffix + q[a];
          for (int t : {q[d], mod(q[d] - 1)})
            candidate.cuts[d][t] |= Mask(1) << suffix;
        }
      }
    if (agrees)
      result.push_back(move(candidate));
  }
  return result;
}

int main(int argc, char **argv) {
  if (argc != 5)
    return 2;
  readAtlas(argv[1]);
  buildCutIndex();
  indexFirstThreeLayers();
  string profile = argv[3];
  if (profile.size() != 4 || !is_sorted(profile.begin(), profile.end()) ||
      profile[0] != '1' || profile.find_first_not_of("123") != string::npos)
    return 2;
  int adjacent = count(profile.begin(), profile.end(), '1');
  vector<Mark> marks;
  for (int d = adjacent; d < 4; d++)
    for (int start : {mod(-int(profile[d] - '0')), 0})
      marks.push_back({d, start});
  ifstream in(argv[2]);
  ofstream out(argv[4]);
  string line;
  int read = 0, surviving = 0;
  while (getline(in, line)) {
    istringstream fields(line);
    vector<Point> fixed;
    int id;
    Space available;
    available.set();
    while (fields >> id) {
      if (id < 0 || id >= 2401)
        return 2;
      auto p = coordinates(id);
      fixed.push_back(p);
      for (int i = 0; i < 81; i++) {
        Point q;
        int t = i;
        for (int a = 0; a < 4; a++, t /= 3)
          q[a] = mod(p[a] + t % 3 - 1);
        available.reset(siteId(q));
      }
    }
    vector<vector<Candidate>> domains;
    for (auto m : marks)
      domains.push_back(candidates(m, adjacent, fixed, available));
    vector<int> chosen(marks.size());
    auto matching = [&](auto &&self, int j) -> bool {
      if (j == int(marks.size()))
        return true;
      for (int n = 0; n < int(domains[j].size()); n++) {
        bool fits = true;
        for (int k = 0; k < j; k++) {
          int a = marks[j].axis, b = marks[k].axis;
          if (a != b &&
              domains[j][n].cuts[otherAxis(a, b)][marks[k].start] !=
                  domains[k][chosen[k]].cuts[otherAxis(b, a)][marks[j].start]) {
            fits = false;
            break;
          }
        }
        if (fits) {
          chosen[j] = n;
          if (self(self, j + 1))
            return true;
        }
      }
      return false;
    };
    bool yes = matching(matching, 0);
    cout << read++ << " domains";
    for (auto &d : domains)
      cout << ' ' << d.size();
    cout << (yes ? " MATCH\n" : " EXCLUDED\n");
    if (yes) {
      surviving++;
      out << line << '\n';
    }
  }
  out.close();
  if (!in.eof() || !out)
    return 2;
  cout << "Nonadjacent projections retain " << surviving << " of " << read
       << " slab unions\n";
}
