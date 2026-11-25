// Necessary conditions for the twelve almost-full neighbors of six solid planes.
// c++ -std=c++17 -O3 filter_85.cpp -o /tmp/filter85
// /tmp/filter85 /tmp/cube85-six.bin /tmp/cube85-residual.bin
#include "plane_record.hpp"

#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <stdexcept>
#include <vector>

namespace {
#ifndef PACKING_SIDE
#define PACKING_SIDE 85
#endif
constexpr int side = PACKING_SIDE;
constexpr int m = (side - 1) / 4;
static_assert(side >= 5 && side % 8 == 5 && coordinates_fit(side));
using Mask = std::bitset<side>;
using Grid = std::array<Mask, side>;
using Record = PlaneRecord;

int mod(int value) {
    int residue = value % side;
    return residue < 0 ? residue + side : residue;
}

struct Pattern {
    Mask holes;
    Mask points;
};

std::array<int, side> inverse{};
std::array<Mask, side> center_rows{};
std::array<Pattern, side> patterns;

void initialize() {
    for (int h = 0; h < side; ++h) {
        Pattern p;
        p.holes.set(h);
        for (int u = 2; u < side; u += 2) p.points.set(mod(h + u));
        patterns[h] = p;
    }
    std::vector<int> slopes;
    for (int divisor = 1; divisor <= m; ++divisor) {
        if (m % divisor == 0) {
            slopes.push_back(2*divisor);
            slopes.push_back(-2*divisor);
        }
    }
    for (int s : slopes) {
        int r = mod(s);
        for (int t = 1; t < side; ++t)
            if (mod(s * t) == 1) inverse[r] = t;
        for (int v = 0; v < side; ++v) {
            int twice = 0;
            for (int u = 0; u < side; ++u) {
                int occupied = patterns[mod(s * u)].points[v];
                twice += u % 2 ? -occupied : occupied;
            }
            assert(twice == 0 || twice == 2);
            center_rows[r][v] = (twice == 2);
        }
    }
}

struct Plane {
    int axis, height, slope, intercept;
    int first() const { return axis == 0 ? 1 : 0; }
    int second() const { return axis == 2 ? 1 : 2; }

    int hole(int input_axis, int coordinate) const {
        if (input_axis == first()) return mod(slope * coordinate + intercept);
        return mod(inverse[slope] * (coordinate - intercept));
    }
    bool contains(int input_axis, int coordinate, int other) const {
        int u = input_axis == first() ? coordinate : other;
        int v = input_axis == first() ? other : coordinate;
        return center_rows[slope][mod(v - slope * u - intercept)];
    }
};
using Six = std::array<std::array<Plane, 2>, 3>;

Six decode(const Record& r) {
    Six full;
    for (int i = 0; i < 3; ++i) {
        for (int t = 0; t < 2; ++t) {
            int slope = r[3 + 4*i + 2*t], intercept = r[4 + 4*i + 2*t];
            if (slope >= side || !inverse[slope] || intercept >= side)
                throw std::runtime_error("invalid full plane");
            full[i][t] = {i, t * r[i], slope, intercept};
        }
    }
    return full;
}

struct GapCatalog {
    static constexpr int limit = side / 2;
    std::map<std::pair<int, int>, Mask> allowed;
    int smallest = side;

    void add(const Record& row) {
        for (int i = 0; i < 3; ++i) {
            int a = row[i], b = row[(i+1)%3], c = row[(i+2)%3];
            if (a < 1 || a > limit || b > limit || c > limit)
                throw std::runtime_error("invalid full-level distance");
            allowed[std::minmax(b, c)].set(a);
            smallest = std::min(smallest, a);
        }
    }

    std::array<int,3> shared_bounds(const Record& row) const {
        std::array<int,3> lower{};
        for (int i = 0; i < 3; ++i) {
            int a = row[i];
            const auto& steps = allowed.at(std::minmax(row[(i+1)%3], row[(i+2)%3]));
            int count = 2;
            for (int t = 1; t < side; ++t) {
                if (t == a) continue;
                int diff = std::abs(t-a);
                if (steps[std::min(t,side-t)] && steps[std::min(diff,side-diff)]) ++count;
            }
            lower[i] = std::max(0, m - (count-1));
        }
        return lower;
    }
};

Mask line(const Grid& grid, int dimension, int u) {
    if (dimension == 0) return grid[u];
    Mask result;
    for (int z = 0; z < side; ++z) result[z] = grid[z][u];
    return result;
}

struct Conditions {
    Mask hole, covered, point, empty, shareable;
    int required_share;
    bool allows(const Pattern& p) const {
        return (hole & ~p.holes).none() && (covered & p.holes).none()
            && (point & ~p.points).none() && (empty & p.points).none()
            && static_cast<int>((shareable & p.points).count()) >= required_share;
    }
};

struct Consensus {
    Mask holes, covered, points, empty;
    int count = 0;
    Consensus() { holes.set(); covered.set(); points.set(); empty.set(); }
    void accept(const Pattern& p) {
        holes &= p.holes; covered &= ~p.holes;
        points &= p.points; empty &= ~p.points;
        ++count;
    }
};

// A transition q_t -> q_(t+1) covers edge t with either one point or a hole.
// Forward and backward tables maximize shareable points at fixed hole count.
void include_one_loss(const Conditions& c, Consensus& common) {
    Mask possible_hole, possible_covered, possible_point, possible_empty;
    bool any = false;
    bool edge[side][2][2]{};
    for (int t=0; t<side; ++t) for (int a : {0,1}) for (int b : {0,1}) {
        if (a && b) continue;
        bool hole = !a && !b;
        edge[t][a][b] = (!c.hole[t] || hole) && (!c.covered[t] || !hole)
                      && (!c.point[t] || a) && (!c.empty[t] || !a);
    }
    using Table = std::array<std::array<std::array<int,4>,2>,side+1>;
    for (int start : {0,1}) {
        Table left, right;
        for (auto& position : left) for (auto& ending : position) ending.fill(-side-1);
        for (auto& position : right) for (auto& ending : position) ending.fill(-side-1);
        left[0][start][0] = right[side][start][0] = 0;
        for (int t=0; t<side; ++t) for (int a : {0,1}) for (int b : {0,1}) {
            if (!edge[t][a][b]) continue;
            int h = 1-a-b, gain = a && c.shareable[t];
            for (int used=0; used+h<=3; ++used)
                left[t+1][b][used+h] = std::max<int>(left[t+1][b][used+h],
                                                      left[t][a][used]+gain);
        }
        if (left[side][start][3] < c.required_share) continue;
        any = true;
        for (int t=side-1; t>=0; --t) for (int a : {0,1}) for (int b : {0,1}) {
            if (!edge[t][a][b]) continue;
            int h = 1-a-b, gain = a && c.shareable[t];
            for (int used=0; used+h<=3; ++used)
                right[t][a][used+h] = std::max<int>(right[t][a][used+h],
                                                     right[t+1][b][used]+gain);
        }
        for (int t=0; t<side; ++t) for (int a : {0,1}) for (int b : {0,1}) {
            if (!edge[t][a][b]) continue;
            int h = 1-a-b, gain = a && c.shareable[t];
            for (int used=0; used+h<=3; ++used) {
                if (left[t][a][used]+gain+right[t+1][b][3-used-h] < c.required_share) continue;
                (h ? possible_hole : possible_covered).set(t);
                (a ? possible_point : possible_empty).set(t);
                break;
            }
        }
    }
    if (any) {
        common.holes &= ~possible_covered; common.covered &= ~possible_hole;
        common.points &= ~possible_empty; common.empty &= ~possible_point;
        ++common.count;
    }
}

class Neighbor {
    const Plane& base;
    const Six& full;
    Grid present{}, absent{}, holes{}, covered{};
    std::array<Grid, 2> required{}, prohibited{};
    bool changed = true;
    bool examine_one_loss;
    std::array<int,3> shared_lower;

    void mark(Mask& mask, int i) {
        if (!mask[i]) { mask.set(i); changed = true; }
    }
    void mark(Grid& grid, int d, int u, int v) {
        if (d == 0) mark(grid[u], v);
        else mark(grid[v], u);
    }
    bool seed(int direction) {
        int shared = mod(base.height + (direction > 0));
        int neighbor = mod(base.height + direction);
        for (int j : {base.first(), base.second()}) {
            int d = (j != base.first());
            for (const Plane& p : full[j]) {
                int h = p.hole(base.axis, neighbor);
                required[d][p.height] = patterns[h].points;
                prohibited[d][p.height] = ~patterns[h].points;
                for (int u = 0; u < side; ++u) {
                    if (!p.contains(base.axis, shared, u)) continue;
                    bool found = false;
                    for (int offset = 0; offset < 2; ++offset) {
                        int t = mod(p.height + offset);
                        if (base.contains(j, t, u)) {
                            mark(present, d, t, u);
                            found = true;
                        }
                    }
                    if (!found) return false;
                }
            }
        }
        return true;
    }
    bool enforce_squares() {
        for (int x = 0; x < side; ++x) for (int y = 0; y < side; ++y) {
            if (!present[x][y]) continue;
            for (int dx = -1; dx <= 1; ++dx) for (int dy = -1; dy <= 1; ++dy)
                if (dx || dy) mark(absent[mod(x + dx)], mod(y + dy));
        }
        for (int x = 0; x < side; ++x) for (int y = 0; y < side; ++y) {
            int count = 0, last_x = 0, last_y = 0;
            for (int dx = 0; dx < 2; ++dx) for (int dy = 0; dy < 2; ++dy) {
                int a = mod(x + dx), b = mod(y + dy);
                if (holes[x][y]) mark(absent[a], b);
                if (present[a][b]) mark(covered[x], y);
                if (!absent[a][b]) { ++count; last_x = a; last_y = b; }
            }
            if (!count) mark(holes[x], y);
            if (count == 1 && covered[x][y]) mark(present[last_x], last_y);
        }
        for (int x = 0; x < side; ++x)
            if ((present[x] & absent[x]).any() || (holes[x] & covered[x]).any()) return false;
        return true;
    }
    Conditions conditions(int d, int u) {
        int k = d == 0 ? base.first() : base.second();
        int next = mod(u + 1);
        auto off0 = line(absent, d, u), off1 = line(absent, d, next);
        Conditions c{line(holes, d, u), line(covered, d, u),
                     required[d][u] | line(present, d, u) | line(present, d, next),
                     prohibited[d][u] | (off0 & off1), {}, shared_lower[k]};
        for (const Plane& p : full[k])
            if (p.height == u) c.required_share = m;
        for (int z = 0; z < side; ++z) {
            c.shareable[z] = (!off0[z] && base.contains(k, u, z))
                          || (!off1[z] && base.contains(k, next, z));
            if (required[d][u][z]) {
                if (off0[z]) mark(present, d, next, z);
                if (off1[z]) mark(present, d, u, z);
            }
            if (prohibited[d][u][z]) {
                mark(absent, d, u, z); mark(absent, d, next, z);
            }
        }
        return c;
    }
    bool enforce_lines(int d) {
        std::array<Consensus, side> common;
        std::array<Conditions, side> rules;
        int bad = 0;
        for (int u = 0; u < side; ++u) {
            rules[u] = conditions(d, u);
            for (const auto& p : patterns)
                if (rules[u].allows(p)) common[u].accept(p);
            if (common[u].count == 0) ++bad;
        }
        if (bad > 2) return false;
        for (int u = 0; u < side; ++u) {
            int possible_loss = 2 - bad + (common[u].count == 0);
            if (possible_loss == 2 || (possible_loss == 1 && !examine_one_loss)) continue;
            if (possible_loss == 1) include_one_loss(rules[u], common[u]);
            const auto& c = common[u];
            if (!c.count) return false;
            for (int z = 0; z < side; ++z) {
                if (c.holes[z]) mark(holes, d, u, z);
                if (c.covered[z]) mark(covered, d, u, z);
                if (c.points[z]) mark(required[d][u], z);
                if (c.empty[z]) mark(prohibited[d][u], z);
            }
        }
        return true;
    }
public:
    Neighbor(const Plane& p, const Six& planes, bool allow_one, const std::array<int,3>& lower)
        : base(p), full(planes), examine_one_loss(allow_one), shared_lower(lower) {}

    bool possible(int direction) {
        if (!seed(direction)) return false;
        while (changed) {
            changed = false;
            if (!enforce_squares() || !enforce_lines(0) || !enforce_lines(1)) return false;
        }
        return true;
    }
};

bool survives(const Six& full, bool examine_one_loss, const std::array<int,3>& lower) {
    for (const auto& pair : full) for (const auto& p : pair) {
        for (int direction : {-1, 1}) {
            Neighbor candidate(p, full, examine_one_loss, lower);
            if (!candidate.possible(direction)) return false;
        }
    }
    return true;
}
// In the common (x,y) plane of the candidate let (u,v) be its two
// coordinates. The four known transverse full planes give four points
// that its affine hole line must contain.
int max_full_levels(const Six& s, int axis) {
    const Plane& base = s[axis][0];
    int u = base.first(), v = base.second(), count = 0;
    for (int t = 0; t < side; ++t) {
        std::array<std::pair<int,int>,4> points{{
            {s[u][0].height, s[u][0].hole(axis,t)},
            {s[u][1].height, s[u][1].hole(axis,t)},
            {s[v][0].hole(axis,t), s[v][0].height},
            {s[v][1].hole(axis,t), s[v][1].height}
        }};
        for (int slope = 1; slope < side; ++slope) {
            if (!inverse[slope]) continue;
            bool fits = true;
            for (int i=1; i<4; ++i) {
                if (mod(slope*(points[i].first-points[0].first) - (points[i].second-points[0].second))) fits = false;
            }
            if (fits) { ++count; break; }
        }
    }
    return count;
}

bool survives_homogeneous(const Six& full) {
    std::array<int,3> lower{};
    for (int axis=0; axis<3; ++axis)
        lower[axis] = std::max(0, m + 1 - max_full_levels(full, axis));
    for (const auto& pair : full) {
        bool inward_possible = false;
        for (int direction : {-1, 1}) {
            Neighbor left(pair[0], full, false, lower);
            if (!left.possible(direction)) continue;
            Neighbor right(pair[1], full, false, lower);
            if (right.possible(-direction)) { inward_possible = true; break; }
        }
        if (!inward_possible) return false;
    }
    return true;
}
} // namespace

int main(int argc, char** argv) {
    const bool homogeneous = argc == 4 && std::string(argv[3]) == "--homogeneous";
    if (argc != 3 && !homogeneous) {
        std::cerr << "Usage: filter85 INPUT.bin OUTPUT.bin [--homogeneous]\n"; return 2;
    }
    std::ifstream input(argv[1], std::ios::binary);
    std::ofstream output(argv[2], std::ios::binary);
    if (!input || !output) return 2;
    initialize();
    Record record;
    if (homogeneous) {
        int count = 0, survivors = 0;
        while (read_record<side>(input, record)) {
            ++count;
            if (survives_homogeneous(decode(record))) {
                write_record<side>(output, record);
                ++survivors;
            }
        }
        output.close();
        std::cout << count << " homogeneous orbits, " << survivors << " survive.\n";
        return input.eof() && output && survivors == 0 &&
               ((side == 261 && count == 114) || (side == 301 && count == 38)) ? 0 : 1;
    }
    std::vector<Record> records;
    GapCatalog catalog;
    while (read_record<side>(input, record)) {
        records.push_back(record);
        if constexpr (side != 85) catalog.add(record);
    }
    if (input.gcount() != 0 || !input.eof()) return 2;
    int count = records.size(), after_full_test = 0, survivors = 0;
    for (const auto& r : records) {
        std::array<int,3> lower{};
        bool applicable;
        if constexpr (side == 85) {
            // This input is the surgery-filtered subset, so its gaps cannot
            // bound all full levels. The residue-class proof gives F <= 5.
            applicable = true;
            for (int i = 0; i < 3; ++i)
                applicable &= r[i] % 17 == 0 && r[4+4*i] % 17 == 0;
            lower.fill(m-4);
        } else {
            // Input is the complete catalog. Distances at least three
            // guarantee the two solid levels needed for each axis.
            applicable = catalog.smallest >= 3;
            lower = catalog.shared_bounds(r);
        }
        auto full = decode(r);
        if (applicable && !survives(full, false, lower)) continue;
        ++after_full_test;
        if (!applicable || side == 85 || survives(full, true, lower)) {
            write_record<side>(output, r);
            ++survivors;
        }
    }
    output.close();
    if (!output) return 2;
    std::cout << count << " six-plane orbits tested; " << survivors << " survive.\n";
    if constexpr (side != 85) {
        std::cout << after_full_test << " required the one-loss line check.\n";
        if constexpr (side == 133)
            return count == 8844 && after_full_test == 116 && survivors == 33 ? 0 : 1;
        if constexpr (side == 205)
            return count == 942 && after_full_test == 28 && survivors == 22 ? 0 : 1;
        if constexpr (side == 141)
            return count == 1266 && after_full_test == 2 && survivors == 0 ? 0 : 1;
        return 0;
    }
    return count == 384 && survivors == 0 ? 0 : 1;
}
