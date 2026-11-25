// Realize the middle-layer assignments as physical three-level slabs and
// match one for each adjacent marked pair in a common coordinate system.
#include "middle_record.hpp"
#include <bitset>
#include <map>
#include <numeric>
#include <set>

using Point = array<int, 4>;
using Slab = vector<uint16_t>;
using Space = bitset<2401>;
using Bin = array<vector<int>, 4>;
array<Point, 2401> coordinates;
array<int, 4> profile{1, 1, 1, 1};
int adjacentAxes = 4;

int siteId(const Point &v) { return ((7 * v[0] + v[1]) * 7 + v[2]) * 7 + v[3]; }

Slab realize(const MiddleChoice &choice) {
  array<bool, 343> left{}, right{}, middle{};
  for (int n = 0; n < 33; ++n) {
    int i = atlasSites[choice.first][n];
    left[i] = true;
    middle[i] = ((choice.middle >> n) & 1) != 0;
    right[motions[choice.motion][atlasSites[choice.second][n]]] = true;
  }
  Slab words;
  for (int i = 0; i < 343; ++i) {
    Point p{0, mod(i / 49 - choice.centers[0]),
            mod(i / 7 % 7 - choice.centers[1]), mod(i % 7 - choice.centers[2])};
    if (middle[i]) {
      if (!left[i] || !right[i])
        throw runtime_error("middle outside intersection");
      words.push_back(siteId(p));
    } else {
      if (left[i]) {
        p[0] = 6;
        words.push_back(siteId(p));
      }
      if (right[i]) {
        p[0] = 1;
        words.push_back(siteId(p));
      }
    }
  }
  if (words.size() != size_t(66 - choice.middleSize))
    throw runtime_error("incorrect slab size");
  return words;
}

array<set<Slab>, 4> enumerateSlabs(istream &input) {
  array<set<Slab>, 4> seen;
  MiddleChoice choice;
  array<uint32_t, 6> matchingImages;
  while (input.read(reinterpret_cast<char *>(&choice), sizeof(choice))) {
    if (!input.read(reinterpret_cast<char *>(matchingImages.data()),
                    sizeof(matchingImages)))
      throw runtime_error("truncated six-band record");
    const Slab words = realize(choice);
    auto gaps = transverseDistances(choice.distanceCode);
    array<int, 4> sourceProfile{1, gaps[0], gaps[1], gaps[2]};
    array<int, 4> firstFrame{0, 1, 2, 3};
    stable_sort(firstFrame.begin(), firstFrame.end(), [&](int a, int b) {
      return sourceProfile[a] < sourceProfile[b];
    });
    for (int a = 0; a < 4; a++)
      if (sourceProfile[firstFrame[a]] != profile[a])
        throw runtime_error(
            "input slab belongs to a different distance profile");
    array<int, 4> axes{0, 1, 2, 3};
    do {
      bool preservesDistances = true;
      for (int a = 0; a < 4; a++)
        if (sourceProfile[axes[a]] != profile[a])
          preservesDistances = false;
      if (!preservesDistances)
        continue;
      int normal = int(find(axes.begin(), axes.end(), 0) - axes.begin());
      for (int signs = 0; signs < 16; ++signs) {
        // Keep the S normalization of the distinguished first slab. Relative
        // to that frame, the other slabs need all signed axis permutations.
        if (normal == 0 && (signs != 0 || axes != firstFrame))
          continue;
        Slab transformed;
        for (int id : words) {
          Point p;
          for (int a = 0; a < 4; ++a) {
            int u = coordinates[id][axes[a]];
            p[a] = ((signs >> a) & 1) ? mod(1 - profile[a] - u) : u;
          }
          transformed.push_back(siteId(p));
        }
        sort(transformed.begin(), transformed.end());
        seen[normal].insert(move(transformed));
      }
    } while (next_permutation(axes.begin(), axes.end()));
  }
  if (!input.eof() || input.gcount())
    throw runtime_error("invalid six-band input");
  return seen;
}

struct Candidate {
  Slab words;
  array<int, 4> face{};
};

struct Active {
  array<int, 4> face;
  Space occupied, forbidden;
};

// Each intersection is the list of *physical* four-coordinate IDs. Identical
// integer labels therefore mean equality of the complete overlap.
array<vector<Active>, 4> reduceCandidates(const array<set<Slab>, 4> &slabs) {
  map<Slab, int> label;
  array<vector<Candidate>, 4> candidates;
  for (int a = 0; a < adjacentAxes; ++a)
    for (const Slab &words : slabs[a]) {
      Candidate candidate{words, {}};
      for (int b = 0; b < adjacentAxes; ++b)
        if (b != a) {
          Slab face;
          for (int id : words)
            if (coordinates[id][b] == 6 || coordinates[id][b] < 2)
              face.push_back(id);
          candidate.face[b] =
              label.emplace(move(face), label.size()).first->second;
        }
      candidates[a].push_back(move(candidate));
    }
  Bin live;
  for (int a = 0; a < 4; ++a) {
    live[a].resize(candidates[a].size());
    iota(live[a].begin(), live[a].end(), 0);
  }
  bool changed;
  do {
    changed = false;
    for (int a = 0; a < 4; ++a)
      for (int b = 0; b < adjacentAxes; ++b)
        if (a != b) {
          vector<bool> present(label.size());
          for (int j : live[b])
            present[candidates[b][j].face[a]] = true;
          auto &v = live[a];
          auto end = remove_if(v.begin(), v.end(), [&](int j) {
            return !present[candidates[a][j].face[b]];
          });
          if (end != v.end()) {
            changed = true;
            v.erase(end, v.end());
          }
        }
  } while (changed);
  array<Space, 2401> neighbors{};
  for (int id = 0; id < 2401; ++id) {
    Point q = coordinates[id];
    for (int i = 0; i < 81; ++i) {
      int digits = i;
      Point p;
      for (int a = 0; a < 4; ++a, digits /= 3)
        p[a] = mod(q[a] + digits % 3 - 1);
      int index = siteId(p);
      if (index != id)
        neighbors[id].set(index);
    }
  }
  array<vector<Active>, 4> result;
  for (int a = 0; a < 4; ++a)
    for (int j : live[a]) {
      const auto &c = candidates[a][j];
      Active ready{c.face, {}, {}};
      for (int id : c.words) {
        ready.occupied.set(id);
        ready.forbidden |= neighbors[id];
      }
      if ((ready.occupied & ready.forbidden).any())
        throw runtime_error("nonindependent slab");
      result[a].push_back(move(ready));
    }
  return result;
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 5)
    return 2;
  if (argc == 5) {
    string description = argv[4];
    if (description.size() != 4 || description[0] != '1' ||
        description.find_first_not_of("123") != string::npos ||
        !is_sorted(description.begin(), description.end()))
      throw runtime_error("expected four sorted distances beginning with 1");
    for (int a = 0; a < 4; a++)
      profile[a] = description[a] - '0';
    adjacentAxes = count(profile.begin(), profile.end(), 1);
  }
  readAtlas(argv[1]);
  ifstream input(argv[2], ios::binary);
  ofstream output(argv[3]);
  if (!input || !output)
    return 2;
  for (int i = 0; i < 2401; ++i)
    coordinates[i] = {i / 343, i / 49 % 7, i / 7 % 7, i % 7};
  const auto slabs = enumerateSlabs(input);
  const auto active = reduceCandidates(slabs);
  cout << "Slabs";
  for (const auto &v : slabs)
    cout << ' ' << v.size();
  cout << "\nAfter overlap checks";
  for (const auto &v : active)
    cout << ' ' << v.size();
  cout << '\n';
  using Lookup = unordered_map<int, vector<int>>;
  array<array<Lookup, 4>, 4> matching;
  for (int a = 0; a < 4; ++a)
    for (int b = 0; b < adjacentAxes; ++b)
      if (a != b)
        for (int j = 0; j < int(active[a].size()); ++j)
          matching[a][b][active[a][j].face[b]].push_back(j);

  array<int, 4> chosen{};
  int count = 0;
  auto join = [&](auto &&self, int axis, Space occupied,
                  Space forbidden) -> void {
    if (axis == adjacentAxes) {
      ++count;
      for (int i = 0; i < 2401; ++i)
        if (occupied[i])
          output << i << ' ';
      output << '\n';
      return;
    }
    const vector<int> *shortest = nullptr;
    for (int b = 0; b < axis; ++b) {
      auto entry = matching[axis][b].find(active[b][chosen[b]].face[axis]);
      if (entry == matching[axis][b].end())
        return;
      if (!shortest || entry->second.size() < shortest->size())
        shortest = &entry->second;
    }
    size_t n = shortest ? shortest->size() : active[axis].size();
    for (size_t k = 0; k < n; ++k) {
      int j = shortest ? (*shortest)[k] : int(k);
      const auto &c = active[axis][j];
      if ((c.occupied & forbidden).any())
        continue;
      bool fits = true;
      for (int b = 0; b < axis; ++b)
        if (c.face[b] != active[b][chosen[b]].face[axis])
          fits = false;
      if (fits) {
        chosen[axis] = j;
        self(self, axis + 1, occupied | c.occupied, forbidden | c.forbidden);
      }
    }
  };
  join(join, 0, {}, {});
  output.close();
  if (!output)
    return 1;
  if (adjacentAxes == 4)
    cout << "Independent four-slab unions " << count << '\n';
  else
    cout << "Independent " << adjacentAxes << "-slab unions " << count << '\n';
}
