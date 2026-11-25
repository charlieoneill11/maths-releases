#include "plane_record.hpp"

#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {
#ifndef PACKING_SIDE
#define PACKING_SIDE 85
#endif
constexpr int side = PACKING_SIDE;
static_assert(side >= 69 && side % 8 == 5 && coordinates_fit(side));
constexpr int m = (side - 1) / 4;
using Mask = std::bitset<side>;
using Record = PlaneRecord;

int mod(int x, int n = side) {
    int r = x % n;
    return r < 0 ? r + n : r;
}
Mask bit(int i) { return Mask(1) << i; }
int weight(const Mask& mask) { return static_cast<int>(mask.count()); }
bool line_contains(int value, int hole) {
    int delta = mod(value - hole);
    return delta > 0 && delta % 2 == 0;
}

std::array<std::array<bool, side>, side> centers{};
std::array<int, side> inverses{};
std::array<bool, side> use_class{};

void initialize() {
    std::vector<int> slopes;
    for (int a = 1; a <= m; ++a) {
        if (m % a == 0) {
            slopes.push_back(2*a);
            slopes.push_back(-2*a);
        }
    }
    for (int signed_slope : slopes) {
        int s = mod(signed_slope);
        for (int i = 1; i < side; ++i)
            if (mod(s * i) == 1) inverses[s] = i;
        for (int v = 0; v < side; ++v) {
            int alternating = 0;
            for (int u = 0; u < side; ++u)
                if (line_contains(v, s * u)) alternating += (u % 2 ? -1 : 1);
            if (alternating != 0 && alternating != 2)
                throw std::runtime_error("invalid planar reconstruction");
            centers[s][v] = alternating == 2;
        }
        for (int u = 0; u < side; ++u)
            for (int v = 0; v < side; ++v) {
                int covered = 0;
                for (int du : {0,1}) for (int dv : {0,1})
                    covered += centers[s][mod(v + dv - s * (u + du))];
                if (covered != (mod(v - s * u) != 0))
                    throw std::runtime_error("inconsistent planar hole");
            }
    }
}

struct Slab {
    int axis, height, slope, intercept;
    int first_axis() const { return axis == 0 ? 1 : 0; }
    int second_axis() const { return axis == 2 ? 1 : 2; }
    int hole(int known_axis, int value) const {
        return known_axis == first_axis() ? mod(slope * value + intercept)
                                          : mod(inverses[slope] * (value - intercept));
    }
    bool contains(int known_axis, int known, int other) const {
        int u = known_axis == first_axis() ? known : other;
        int v = known_axis == first_axis() ? other : known;
        return centers[slope][mod(v - slope * u - intercept)];
    }
};
using Slabs = std::array<std::array<Slab,2>,3>;

// Removing an original pair and inserting a new pair gives two retained
// intervals, displaced by zero or two after choosing a parent phase.
// Actions 0,1 retain adjacent levels with common displacement 0,2.
// Action 2 separates the levels by an insertion; 3 discards the line.
struct CoordinateMap {
    int actions[2]{};
    Mask retained[2]{};
};

std::vector<CoordinateMap> coordinate_maps(const std::array<Slab,2>& pins) {
    std::vector<CoordinateMap> result;
    result.reserve(side * (side - 2));
    for (int removed = 0; removed < side; ++removed) {
        for (int cut = 1; cut <= side - 2; ++cut) {
            CoordinateMap map;
            for (int x = 0; x < side; ++x) {
                int order = mod(x - removed - 2);
                if (order < side - 2) map.retained[order >= cut] |= bit(x);
            }
            for (int pin = 0; pin < 2; ++pin) {
                int order = mod(pins[pin].height - removed - 2);
                int next = (order + 1) % side;
                if (order >= side - 2 || next >= side - 2) map.actions[pin] = 3;
                else if (order >= cut) map.actions[pin] = 1;
                else map.actions[pin] = next >= cut ? 2 : 0;
            }
            result.push_back(map);
        }
    }
    return result;
}

struct Errors { Mask positions[2]{}; };
using Allowed = std::array<std::array<Mask, 16>,16>;

Allowed allowed_phases(const Slab& base, const std::array<Slab,2>& pins,
                       const std::vector<CoordinateMap>& cross_maps, int direction) {
    Errors errors[2][3][side]{};
    const int shared = mod(base.height + (direction > 0));
    const int neighbor = mod(base.height + direction);
    for (int line = 0; line < 2; ++line) {
        const auto& pin = pins[line];
        const int h = pin.hole(base.axis, neighbor);
        int known_side[side];
        for (int z = 0; z < side; ++z) {
            known_side[z] = -1;
            if (pin.contains(base.axis, shared, z)) {
                bool lower = base.contains(pin.axis, pin.height, z);
                bool upper = base.contains(pin.axis, pin.height + 1, z);
                if (lower == upper) throw std::runtime_error("incompatible pinned site");
                known_side[z] = upper;
            }
        }
        for (int action = 0; action < 3; ++action) {
            int lower = pin.height + 2 * (action == 1);
            int upper = lower + 1 + 2 * (action == 2);
            for (int phase = 0; phase < side; ++phase) {
                Slab parent = base;
                parent.intercept = phase;
                for (int jump : {0,1}) for (int z = 0; z < side; ++z) {
                    bool on_lower = parent.contains(pin.axis, lower, z + 2 * jump);
                    bool on_upper = parent.contains(pin.axis, upper, z + 2 * jump);
                    int occupied = int(on_lower) + int(on_upper);
                    if (occupied != int(line_contains(z, h)) ||
                        (known_side[z] == 0 && !on_lower) ||
                        (known_side[z] == 1 && !on_upper))
                        errors[line][action][phase].positions[jump] |= bit(z);
                }
            }
        }
    }
    Allowed allowed{};
    for (const auto& map : cross_maps) {
        int cross_actions = 4 * map.actions[0] + map.actions[1];
        Mask possible[2][4]{};
        possible[0][3] = possible[1][3] = ~Mask{};
        for (int line = 0; line < 2; ++line)
            for (int action = 0; action < 3; ++action)
                for (int phase = 0; phase < side; ++phase) {
                    const auto& e = errors[line][action][phase];
                    Mask bad = (e.positions[0] & map.retained[0]) |
                               (e.positions[1] & map.retained[1]);
                    if (weight(bad) <= 2) possible[line][action] |= bit(phase);
                }
        for (int a = 0; a < 4; ++a) for (int b = 0; b < 4; ++b)
            allowed[4*a+b][cross_actions] |= possible[0][a] & possible[1][b];
    }
    return allowed;
}

bool matching_parent_possible(const Slabs& full, const Slab& base, int direction) {
    const auto& x = full[base.first_axis()];
    const auto& y = full[base.second_axis()];
    auto columns = allowed_phases(base, x, coordinate_maps(y), direction);
    auto rows = allowed_phases(base, y, coordinate_maps(x), direction);
    for (int i = 0; i < 16; ++i) for (int j = 0; j < 16; ++j)
        if ((columns[i][j] & rows[j][i]).any()) return true;
    return false;
}

bool passes_surgery(const Record& record) {
    Slabs full;
    for (int i = 0; i < 3; ++i) for (int j = 0; j < 2; ++j) {
        int s = record[3 + 4 * i + 2 * j];
        if (s >= side || !inverses[s] || record[i] == 0 || record[i] >= side ||
            record[4 + 4 * i + 2 * j] >= side)
            throw std::runtime_error("invalid full slab");
        full[i][j] = {i, j ? record[i] : 0, s, record[4 + 4 * i + 2 * j]};
    }
    for (const auto& axis : full) for (const auto& base : axis) {
        int magnitude = std::min(base.slope, side - base.slope);
        int d = magnitude / 2;
        int base_class = std::min(d, m/d);
        if (!use_class[base_class]) continue;
        for (int direction : {-1,1})
            if (!matching_parent_possible(full, base, direction)) return false;
    }
    return true;
}

std::vector<int> digits(int n, int a) {
    std::vector<int> result(n);
    for (int j = 0; j < (n-1)/(4*a); ++j)
        for (int i = 0; i < a; ++i) result[2*i + 4*a*j] = 1;
    return result;
}

int seam_overlap(int base_class, int parent_side, int parent_slope, int jump) {
    auto base = digits(side, base_class);
    auto parent = digits(parent_side, std::abs(parent_slope)/2);
    int best = 0;
    for (int c = 0; c < side; ++c) for (int d = 0; d < parent_side; ++d) {
        int counts[2][side][side+1]{};
        for (int y = 0; y < side; ++y) for (int ys : {0,1}) {
            int all_shifted = 0;
            auto& row = counts[ys][y];
            for (int x = 0; x < side; ++x) {
                // Transposing both planes puts their first coordinate along each prefix.
                int present = base[mod(x - 2*base_class*y + c)];
                int phase = mod(x - parent_slope * (y + ys*jump) + d, parent_side);
                int shifted = parent[mod(phase+jump,parent_side)];
                all_shifted += present * shifted;
                row[x+1] = present * (parent[phase] - shifted);
            }
            row[0] = all_shifted;
            for (int cut = 1; cut <= side; ++cut) row[cut] += row[cut-1];
        }
        for (int cut_x = 0; cut_x <= side; ++cut_x) {
            int initial = 0, prefix = 0, largest = 0;
            for (int y = 0; y < side; ++y) {
                initial += counts[1][y][cut_x];
                prefix += counts[0][y][cut_x] - counts[1][y][cut_x];
                largest = std::max(largest, prefix);
            }
            best = std::max(best, initial + largest);
        }
    }
    return best;
}

bool verify_other_parents(int base_class) {
    // The alternating slab count bounds the deviation of each physical
    // layer from (m*side-1)/2 by F-1, with F at most the side length.
    constexpr int shared_minimum = (m*side-1)/2 - (side-1);
    bool separated = true;
    for (int k : {side-4, side, side+4}) {
        int largest = 0;
        for (int a = 1; a <= (k-1)/4; ++a) {
            if (((k-1)/4)%a) continue;
            for (int s : {-2*a,2*a}) {
                if (k == side && s == 2*base_class) continue;
                largest = std::max(largest, seam_overlap(base_class,k,s,k < side ? -2 : 2));
            }
        }
        int bound = largest + (k < side ? 8*m : k == side ? 4*m : 0) + 2*m;
        std::cout << "class " << base_class << ", ordinary parent " << k
                  << ", retained overlap " << largest << ", bound " << bound
                  << ", shared floor " << shared_minimum << std::endl;
        if (bound >= shared_minimum) separated = false;
        if (k == side + 4) {
            // The localized lift changes old-grid sites in one primal column.
            const int double_bound = largest + m + 2*m;
            std::cout << "class " << base_class << ", double expansion parent " << k
                      << ", bound " << double_bound << ", shared floor "
                      << shared_minimum << std::endl;
            if (double_bound >= shared_minimum) separated = false;
        }
    }
    return separated;
}
}  // namespace

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "usage: verify_85_surgery SIX_FULL_SLAB_RECORDS SURVIVING_RECORDS\n";
        return 2;
    }
    initialize();
    for (int d=2; d*d<=m; ++d) {
        if (m%d==0) use_class[d] = verify_other_parents(d);
    }
    std::ifstream input(argv[1],std::ios::binary);
    if (!input) throw std::runtime_error("cannot open skeleton records");
    std::ofstream output(argv[2],std::ios::binary);
    if (!output) throw std::runtime_error("cannot open survivor file");
    Record record;
    int count = 0, passed = 0;
    while (read_record<side>(input, record)) {
        ++count;
        if (passes_surgery(record)) {
            write_record<side>(output, record);
            ++passed;
        }
    }
    if (input.gcount() || !input.eof() || count == 0)
        throw std::runtime_error("invalid skeleton file");
    std::cout << "skeletons " << count << ", survivors " << passed << '\n';
    output.close();
    if (!output) throw std::runtime_error("failed writing survivor file");
    if (side==85 && (count!=5558 || passed!=384))
        throw std::runtime_error("unexpected side-85 filter counts");
    if (side==133 && (count!=33 || passed!=0))
        throw std::runtime_error("unexpected side-133 filter counts");
    if (side==205 && (count!=22 || passed!=0))
        throw std::runtime_error("unexpected side-205 filter counts");
}
