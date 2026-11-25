// Exhaust the terminal-colour exclusions (F1)-(F4) for the three blocks of the paper, Section 6.
// Compile with c++ -std=c++17 -O3 replay_blocks.cpp -o /tmp/replay-blocks.
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <utility>
#include <vector>

using Edge = std::pair<int, int>;
struct Matching {
    unsigned edges;
    unsigned vertices;
};

class BlockSearch {
public:
    BlockSearch(int type, int numerator, int denominator)
        : p(numerator), q(denominator), sizes(p), occupied(p), terminal(p), options(p) {
        std::vector<Edge> omitted;
        if (type != 3) omitted.emplace_back(0,1);
        if (type == 1) {
            add_path(omitted, {0,2,3,1});
            add_path(omitted, {0,4,5,6,7,8,1});
        } else if (type == 2) {
            add_path(omitted, {0,2,1});
            add_path(omitted, {0,3,4,5,6,7,8,1});
        } else {
            add_path(omitted, {0,2,1});
            add_path(omitted, {0,3,4,0});
            add_path(omitted, {1,5,6,7,8,1});
        }
        for (int u = 0; u < 9; ++u) {
            for (int v = u+1; v < 9; ++v) {
                if (std::find(omitted.begin(), omitted.end(), Edge{u,v}) == omitted.end()) {
                    graph.emplace_back(u, v);
                }
            }
        }
        if (graph.size() != 26) throw std::logic_error("wrong core");
        enumerate_matchings(0, {0,0}, 0);
    }

    bool possible(int other, bool all_slots = true) {
        std::fill(terminal.begin(), terminal.end(), 0);
        terminal[0] |= 1u;
        terminal[other] |= 2u;
        if (p == 27 && all_slots) {
            // At a new threshold all 27 slots are occupied by the 28 edges.
            for (int twice = 0; twice < p; ++twice) {
                for (int i = 0; i < p; ++i)
                    sizes[i] = 1 + (i == twice) - (i == 0) - (i == other);
                if (try_schedule()) return true;
            }
        } else {
            std::vector<int> windows(p, 4);
            return deficits(windows, 4*p-26*q, 0);
        }
        return false;
    }

private:
    int p, q;
    std::vector<Edge> graph;
    std::array<std::vector<Matching>, 5> matchings;
    std::vector<int> sizes, order;
    std::vector<unsigned> occupied, terminal;
    std::vector<std::array<std::vector<Matching>, 512>> options;

    static void add_path(std::vector<Edge> &edges, const std::vector<int> &path) {
        for (size_t j = 1; j < path.size(); ++j)
            edges.push_back(std::minmax(path[j-1], path[j]));
    }

    void enumerate_matchings(int start, Matching chosen, int count) {
        matchings[count].push_back(chosen);
        if (count == 4) return;
        for (int i = start; i < int(graph.size()); ++i) {
            auto [u,v] = graph[i];
            unsigned pair = (1u<<u) | (1u<<v);
            if (!(pair & chosen.vertices))
                enumerate_matchings(i+1, {chosen.edges | (1u<<i), chosen.vertices | pair}, count+1);
        }
    }

    int index(int i) const { return (i+p)%p; }

    bool deficits(std::vector<int> &windows, int left, int start) {
        if (left > 0) {
            for (int i = start; i < p; ++i) {
                --windows[i];
                bool found = deficits(windows, left-1, i);
                ++windows[i];
                if (found) return true;
            }
            return false;
        }
        sizes[0] = 0;
        for (int t = 0; t < p; ++t) {
            int i = t*q % p;
            sizes[(i+q)%p] = sizes[i] + windows[(i+1)%p] - windows[i];
        }
        int correction = 26 - std::accumulate(sizes.begin(), sizes.end(), 0);
        if (correction % p) throw std::logic_error("nonintegral schedule");
        for (int &value : sizes) value += correction/p;
        return try_schedule();
    }

    bool try_schedule() {
        for (int i = 0; i < p; ++i) {
            if (sizes[i] < 0 || sizes[i] > 4) return false;
            int endpoints = 0;
            for (int j = 0; j < q; ++j) {
                int t = index(i+j);
                endpoints += 2*sizes[t] + int(terminal[t]&1) + int((terminal[t]>>1)&1);
            }
            if (endpoints > 9) return false;
        }
        // Fix a branching order. Heavily constrained neighbouring slots go early.
        order.clear();
        std::vector<bool> placed(p, false);
        for (int depth = 0; depth < p; ++depth) {
            int best = -1, best_score = 1000;
            for (int i = 0; i < p; ++i) {
                if (placed[i]) continue;
                int used = 0, tips = 0;
                for (int j = 1-q; j < q; ++j) {
                    int t = index(i+j);
                    if (placed[t]) used += 2*sizes[t];
                    tips += int(terminal[t]&1) + int((terminal[t]>>1)&1);
                }
                int score = 15*(sizes[i]+1) - 6*std::min(used+tips,9)
                            - 8*std::max(0,2*sizes[i]+used+tips-8);
                if (!depth) score = 30*sizes[i] - 10*tips;
                if (score < best_score) { best_score = score; best = i; }
            }
            placed[best] = true;
            order.push_back(best);
        }
        for (int i = 0; i < p; ++i) {
            unsigned forbidden = 0;
            for (int j = 1-q; j < q; ++j) forbidden |= terminal[index(i+j)];
            for (unsigned mask = 0; mask < 512; ++mask) {
                auto &choices = options[i][mask];
                choices.clear();
                for (auto m : matchings[sizes[i]])
                    if (!(m.vertices & (mask|forbidden))) choices.push_back(m);
            }
        }
        std::fill(occupied.begin(), occupied.end(), 0);
        return assign(0, 0);
    }

    bool assign(int depth, unsigned used) {
        if (depth == p) return true;
        int i = order[depth];
        unsigned forbidden = 0;
        for (int j = 1-q; j < q; ++j) forbidden |= occupied[index(i+j)];
        for (auto candidate : options[i][forbidden]) {
            if (candidate.edges & used) continue;
            occupied[i] = candidate.vertices;
            if (assign(depth+1, used|candidate.edges)) return true;
        }
        occupied[i] = 0;
        return false;
    }
};

int main() {
    BlockSearch half_grid(2, 13, 2);
    for (int h = 0; h <= 6; ++h)
        if (half_grid.possible(h) != (h == 6))
            throw std::runtime_error("unexpected half-grid terminal difference");
    for (int type : {1,2,3}) {
        BlockSearch grid(type, 20, 3), threshold(type, 27, 4);
        for (int h = 0; h <= 10; ++h)
            if (grid.possible(h) != (h >= 6+type))
                throw std::runtime_error("unexpected (20,3) terminal difference");
        for (int h = 0; h <= 13; ++h)
            if (threshold.possible(h))
                throw std::runtime_error("all 27 slots can be occupied");
        if (type == 3 && threshold.possible(11, false))
            throw std::runtime_error("terminal distance below three in the third block");
        std::cout << "Block " << type << " passed its terminal-colour tests\n";
    }
}
