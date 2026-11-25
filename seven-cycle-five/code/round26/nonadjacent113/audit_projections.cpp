#include "../upper113/atlas.hpp"
#include <map>
#include <set>
int crossIndex(int id, int axis) {
  int p[] = {id / 49, id / 7 % 7, id % 7}, q = 0;
  for (int d = 0; d < 3; d++)
    if (d != axis)
      q = 7 * q + p[d];
  return q;
}
int coordinate(int id, int axis) {
  return (id / (axis == 0 ? 49 : axis == 1 ? 7 : 1)) % 7;
}
Mask window(const Sites &s, int axis, int t) {
  Mask out = 0;
  for (int id : s)
    if ((coordinate(id, axis) - t + 7) % 7 < 2)
      out |= Mask(1) << crossIndex(id, axis);
  return out;
}
Sites image(int rep, int g) {
  Sites s;
  for (int i = 0; i < 33; i++)
    s[i] = motions[g][atlasSites[rep][i]];
  return s;
}
using Key = pair<Mask, Mask>;
struct Layout {
  Sites S, T;
  int t[6];
  Key key[6];
};
struct Cut {
  std::array<Mask, 6> masks{};
  Mask x{}, y{}, left{}, right{};
};
int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  readAtlas(argv[1]);
  std::ifstream f(argv[2]);
  if (!f)
    throw runtime_error("missing layout file");
  std::vector<Layout> layouts;
  std::map<Key, int> contactIds;
  int a, b, g, k, z[3];
  string line;
  while (getline(f, line)) {
    istringstream row(line);
    string extra;
    if (!(row >> a >> b >> g >> k >> z[0] >> z[1] >> z[2]) || row >> extra ||
        a < 0 || a >= 1016 || b < 0 || b >= 1016 || g < 0 || g >= 16464)
      throw runtime_error("invalid audit record");
    Layout c;
    c.S = atlasSites[a];
    c.T = image(b, g);
    for (int j = 0; j < 6; j++) {
      int e = j / 2;
      if (z[e] < 0 || z[e] >= 14)
        throw runtime_error("invalid encoded placement");
      c.t[j] = (z[e] % 7 + (j % 2) * (2 + z[e] / 7)) % 7;
      c.key[j] = {window(c.S, e, c.t[j]), window(c.T, e, c.t[j])};
      contactIds.emplace(c.key[j], contactIds.size());
    }
    layouts.push_back(c);
  }
  if (!f.eof())
    throw runtime_error("layout input failure");
  std::vector<std::vector<Planes>> catalog(contactIds.size());
  std::vector<std::set<Planes>> uniqueSupports(contactIds.size());
  // Reconstruct all seven physical planes by moving the 33 sites, independent
  // of the fast symbolic cut and layer descriptors used by the primary join.
  for (int b = 0; b < 1016; b++)
    for (int g = 0; g < 16464; g++) {
      Planes p{};
      for (int site : atlasSites[b]) {
        int v = motions[g][site];
        p[v / 49] |= Mask(1) << (v % 49);
      }
      auto it = contactIds.find({p[0] | p[1], p[2] | p[3]});
      if (it != contactIds.end()) {
        int ix = it->second;
        if (uniqueSupports[ix].insert(p).second)
          catalog[ix].push_back(p);
      }
    }
  int survivors = 0, planarOnly = 0;
  for (const auto &c : layouts) {
    std::array<std::vector<Cut>, 6> domains;
    for (int j = 0; j < 6; j++) {
      int e = j / 2;
      for (const auto &p : catalog[contactIds.at(c.key[j])]) {
        Sites v;
        int n = 0;
        for (int h = 0; h < 7; h++)
          for (Mask w = p[h]; w; w &= w - 1)
            v[n++] = 49 * h + __builtin_ctzll(w);
        assert(n == 33);
        Cut record;
        for (int h = 0; h < 6; h++)
          if (j / 2 != h / 2)
            record.masks[h] = window(v, 1 + h / 2 - (h / 2 > j / 2), c.t[h]);
        for (int s = 0; s < 2; s++)
          for (int i = 0; i < 33; i++) {
            int site = (s ? c.T : c.S)[i];
            if ((coordinate(site, e) - c.t[j] + 7) % 7 < 2) {
              (s ? record.right : record.left) |= Mask(1) << i;
              if ((p[1 + s] >> crossIndex(site, e)) & 1)
                (s ? record.y : record.x) |= Mask(1) << i;
            }
          }
        domains[j].push_back(record);
      }
    }
    std::array<Mask, 33> confusions{};
    for (int i = 0; i < 33; i++)
      for (int j = 0; j < 33; j++) {
        bool conflict = true;
        for (int d = 0; d < 3; d++) {
          int x = (coordinate(c.S[i], d) - coordinate(c.T[j], d) + 7) % 7;
          if (x >= 2 && x <= 5)
            conflict = false;
        }
        if (conflict)
          confusions[i] |= Mask(1) << j;
      }
    auto fits = [&](int j, const Cut &r, int h, const Cut &s, bool heights) {
      if (j / 2 != h / 2 && r.masks[h] != s.masks[j])
        return false;
      if (!heights)
        return true;
      if (((r.x ^ s.x) & r.left & s.left) || ((r.y ^ s.y) & r.right & s.right))
        return false;
      for (Mask x = r.x | s.x; x; x &= x - 1)
        if (confusions[__builtin_ctzll(x)] & (r.y | s.y))
          return false;
      return true;
    };
    // First test only planar agreement. Repeat with overlaps of the
    // physical A-level memberships and all cross-level conflicts.
    for (bool heights : {false, true}) {
      auto choices = domains;
      bool change = true;
      while (change) {
        change = false;
        for (int j = 0; j < 6; j++)
          for (int h = 0; h < 6; h++)
            if (j != h) {
              auto &v = choices[j];
              auto end = std::remove_if(v.begin(), v.end(), [&](const Cut &r) {
                for (auto &s : choices[h])
                  if (fits(j, r, h, s, heights))
                    return false;
                return true;
              });
              if (end != v.end()) {
                v.erase(end, v.end());
                change = true;
              }
            }
      }
      if (std::any_of(choices.begin(), choices.end(),
                      [](const auto &d) { return d.empty(); }))
        break;
      std::array<const Cut *, 6> chosen;
      auto walk = [&](auto &&self, int j) -> bool {
        if (j == 6)
          return true;
        for (auto &r : choices[j]) {
          bool ok = true;
          for (int h = 0; h < j; h++)
            if (!fits(j, r, h, *chosen[h], heights))
              ok = false;
          if (ok) {
            chosen[j] = &r;
            if (self(self, j + 1))
              return true;
          }
        }
        return false;
      };
      if (walk(walk, 0)) {
        if (heights)
          survivors++;
        else
          planarOnly++;
      } else
        break;
    }
  }
  std::cout << "Independent direct-coordinate audit: " << layouts.size()
            << " layouts, " << planarOnly << " planar-compatible, " << survivors
            << " height-compatible\n";
  return survivors ? 1 : 0;
}
