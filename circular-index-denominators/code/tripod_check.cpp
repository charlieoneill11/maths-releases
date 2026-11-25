// Read the core and roots from replay_tripod.py --emit.
// Independently exhaust the half-grid placements and edge lists.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

class Search {
    static constexpr int order = 13, period = 19;
    std::array<int, 3> roots{}, terminals{};
    std::array<unsigned, period> palette{};
    std::array<unsigned, order> permitted{}, terminal_bits{}, left{};
    std::array<int, period> vertex_at{};
    std::array<std::array<bool, order>, order> adjacent{};
    std::vector<int> label_order;
    std::vector<std::pair<int,int>> edges;
    std::array<bool, 57> assigned{};

    bool colour(int remaining) {
        if (remaining == 0) return true;
        int best = -1, least = period + 1;
        unsigned options = 0;
        for (int i = 0; i < int(edges.size()); ++i) {
            if (assigned[i]) continue;
            auto [u,v] = edges[i];
            unsigned choices = left[u] & left[v];
            int count = std::popcount(choices);
            if (!count) return false;
            if (count < least) {
                least = count;
                best = i;
                options = choices;
            }
        }
        auto [u,v] = edges[best];
        assigned[best] = true;
        for (; options; options &= options - 1) {
            unsigned bit = options & -options;
            left[u] ^= bit;
            left[v] ^= bit;
            bool found = colour(remaining - 1);
            left[u] ^= bit;
            left[v] ^= bit;
            if (found) {
                assigned[best] = false;
                return true;
            }
        }
        assigned[best] = false;
        return false;
    }

    bool label(unsigned used, int depth) {
        if (depth == order) {
            left = permitted;
            return colour(int(edges.size()));
        }
        int h = label_order[depth];
        for (int v = 0; v < order; ++v) {
            if ((used >> v) & 1) continue;
            if ((palette[h] & terminal_bits[v]) != terminal_bits[v]) continue;
            if (h && vertex_at[h-1] >= 0 && adjacent[v][vertex_at[h-1]]) continue;
            unsigned available = palette[h] ^ terminal_bits[v];
            unsigned forced = 0;
            bool possible = true;
            for (int w = 0; w < order; ++w) {
                if (!((used >> w) & 1) || !adjacent[v][w]) continue;
                unsigned intersection = available & permitted[w];
                if (!intersection || (std::has_single_bit(intersection) && (intersection & forced))) {
                    possible = false;
                    break;
                }
                if (std::has_single_bit(intersection)) forced |= intersection;
            }
            if (!possible) continue;
            permitted[v] = available;
            vertex_at[h] = v;
            bool found = label(used | (1u << v), depth + 1);
            vertex_at[h] = -1;
            if (found) return true;
        }
        return false;
    }

public:
    Search() {
        for (int &v : roots) std::cin >> v;
        for (int i = 0; i < 57; ++i) {
            int v, w;
            if (!(std::cin >> v >> w) || v < 0 || w >= order || v >= w || adjacent[v][w])
                throw std::runtime_error("invalid core edge");
            adjacent[v][w] = adjacent[w][v] = true;
            edges.emplace_back(v,w);
        }
        for (int h = 0; h < period; ++h)
            for (int j = 1; j <= 9; ++j) palette[h] |= 1u << ((h + 2*j) % period);
    }

    bool possible(int x, int y) {
        terminals = {0, x, x+y};
        std::vector<std::vector<int>> runs;
        int previous = -2;
        for (int h = 0; h < period; ++h) {
            bool omitted = false;
            for (int c : terminals)
                if (h == c || (h+1) % period == c) omitted = true;
            if (omitted) continue;
            if (previous != h-1) runs.emplace_back();
            runs.back().push_back(h);
            previous = h;
        }
        std::sort(runs.begin(), runs.end(), [](const auto &a, const auto &b) {
            return a.size() > b.size();
        });
        label_order.clear();
        for (const auto &run : runs) label_order.insert(label_order.end(), run.begin(), run.end());
        if (label_order.size() != order) throw std::runtime_error("wrong empty-window count");
        std::sort(roots.begin(), roots.end());
        do {
            terminal_bits.fill(0);
            for (int i = 0; i < 3; ++i) terminal_bits[roots[i]] = 1u << terminals[i];
            vertex_at.fill(-1);
            if (label(0,0)) return true;
        } while (std::next_permutation(roots.begin(), roots.end()));
        return false;
    }
};

int main() {
    Search search;
    int cases = 0;
    for (int x = 2; x <= 6; ++x) {
        for (int y = x; y <= 19; ++y) {
            int z = 19-x-y;
            if (z < y) continue;
            bool allowed = (x == 5 && y == 7) || (x == 6 && y == 6);
            if (search.possible(x,y) != allowed)
                throw std::runtime_error("unexpected terminal placement");
            ++cases;
        }
    }
    std::cout << cases << " terminal gap triples independently checked\n";
}
