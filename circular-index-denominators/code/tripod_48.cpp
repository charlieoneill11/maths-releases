#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>

// Independent finite-domain search. Each choice supplies the colours of one
// core star. Residual column sums account for every internal edge endpoint.
using Mask = std::uint64_t;
constexpr int vertices = 13;
constexpr int slots = 48;
constexpr Mask circle = (Mask{1} << slots) - 1;
Mask flag(int i) { return Mask{1} << i; }
using Counts = std::array<int, slots>;
struct Choice {
    Mask colours;
    Mask holes;
};
struct Search {
    std::array<int, 3> roots{};
    std::array<std::array<bool, vertices>, vertices> adjacent{};
    std::vector<std::pair<int, int>> edges;
    std::vector<Choice> all;
    std::array<std::vector<Choice>, vertices> choices;
    using Domains = std::array<std::vector<int>, vertices>;
    std::array<int, vertices> assignment{};
    Mask single = 0;
    long long calls = 0, complete = 0;
    Search() {
        std::set<Mask> palettes;
        // Form the nine gaps directly from a composition of 48 into
        // integers at least five, with the first colour zero before rotation.
        for (int a = 0; a < 9; ++a)
            for (int b = a; b < 9; ++b)
                for (int c = b; c < 9; ++c) {
                    Mask palette = 0;
                    int pos = 0;
                    for (int j = 0; j < 9; ++j) {
                        palette |= flag(pos);
                        pos += 5 + (j == a) + (j == b) + (j == c);
                    }
                    for (int j = 0; j < slots; ++j) {
                        palettes.insert(palette);
                        palette = ((palette << 1) & circle) | (palette >> 47);
                    }
                }
        for (Mask palette : palettes) {
            Mask holes = 0;
            for (int j = 0; j < slots; ++j) {
                bool covered = false;
                for (int k = 0; k < 5; ++k)
                    covered |= (palette & flag((j + k) % slots)) != 0;
                if (!covered)
                    holes |= flag(j);
            }
            if (std::popcount(holes) != 3)
                throw std::runtime_error("star size");
            all.push_back({palette, holes});
        }
    }
    bool compatible(int v, Choice a, int w, Choice b) const {
        Mask shared = a.colours & b.colours;
        int unique = std::popcount(shared & single);
        return adjacent[v][w] ? shared && unique <= 1 : unique == 0;
    }
    bool assign_edges(Mask left, std::array<Mask, vertices> &available) const {
        if (!left)
            return true;
        int best = -1, smallest = slots + 1;
        Mask options = 0;
        for (Mask e = left; e; e &= e - 1) {
            int i = std::countr_zero(e);
            auto [v, w] = edges[i];
            Mask common = available[v] & available[w];
            int count = std::popcount(common);
            if (!count)
                return false;
            if (count < smallest) {
                best = i;
                smallest = count;
                options = common;
            }
        }
        auto [v, w] = edges[best];
        while (options) {
            Mask entry = options & -options;
            available[v] ^= entry;
            available[w] ^= entry;
            if (assign_edges(left ^ flag(best), available))
                return true;
            available[v] ^= entry;
            available[w] ^= entry;
            options ^= entry;
        }
        return false;
    }
    bool reduce(Domains &domains, int remaining, const Counts &count, const Counts &holes) const {
        bool changed;
        do {
            changed = false;
            std::array<Mask, vertices> lower[2]{}, upper[2]{};
            for (int v = 0; v < vertices; ++v)
                if (remaining & (1 << v)) {
                    if (domains[v].empty())
                        return false;
                    lower[0][v] = lower[1][v] = circle;
                    for (int id : domains[v]) {
                        Choice row = choices[v][id];
                        lower[0][v] &= row.colours;
                        upper[0][v] |= row.colours;
                        lower[1][v] &= row.holes;
                        upper[1][v] |= row.holes;
                    }
                }
            Mask need[2]{}, ban[2]{};
            for (int kind = 0; kind < 2; ++kind) {
                const Counts &demand = kind ? holes : count;
                for (int j = 0; j < slots; ++j) {
                    int low = 0, high = 0;
                    for (int v = 0; v < vertices; ++v) {
                        low += (lower[kind][v] >> j) & 1;
                        high += (upper[kind][v] >> j) & 1;
                    }
                    if (demand[j] < low || demand[j] > high)
                        return false;
                    if (demand[j] == low)
                        ban[kind] |= flag(j);
                    if (demand[j] == high)
                        need[kind] |= flag(j);
                }
            }
            for (int v = 0; v < vertices; ++v)
                if (remaining & (1 << v)) {
                    Mask reqC = need[0] & upper[0][v], reqH = need[1] & upper[1][v];
                    Mask banC = ban[0] & ~lower[0][v], banH = ban[1] & ~lower[1][v];
                    auto &domain = domains[v];
                    auto used = std::remove_if(domain.begin(), domain.end(), [&](int id) {
                        auto row = choices[v][id];
                        return (reqC & ~row.colours) || (reqH & ~row.holes) ||
                               (banC & row.colours) || (banH & row.holes);
                    });
                    changed |= used != domain.end();
                    domain.erase(used, domain.end());
                }
        } while (changed);
        return true;
    }
    bool visit(Domains &domains, int remaining, Counts count, Counts holes) {
        ++calls;
        if (!reduce(domains, remaining, count, holes))
            return false;
        if (!remaining) {
            ++complete;
            std::array<Mask, vertices> available;
            for (int v = 0; v < vertices; ++v)
                available[v] = choices[v][assignment[v]].colours;
            return assign_edges((Mask{1} << edges.size()) - 1, available);
        }
        int best = -1;
        for (int v = 0; v < vertices; ++v)
            if (remaining & (1 << v)) {
                if (best < 0 || domains[v].size() < domains[best].size())
                    best = v;
            }
        int rest = remaining ^ (1 << best);
        for (int id : domains[best]) {
            Choice row = choices[best][id];
            Domains next;
            bool valid = true;
            for (int v = 0; v < vertices && valid; ++v)
                if (rest & (1 << v)) {
                    for (int j : domains[v])
                        if (compatible(best, row, v, choices[v][j]))
                            next[v].push_back(j);
                    valid = !next[v].empty();
                }
            if (!valid)
                continue;
            Counts c = count, h = holes;
            for (Mask m = row.colours; m; m &= m - 1)
                --c[std::countr_zero(m)];
            for (Mask m = row.holes; m; m &= m - 1)
                --h[std::countr_zero(m)];
            assignment[best] = id;
            if (visit(next, rest, c, h))
                return true;
        }
        return false;
    }
    bool solve(const Counts &sizes, const std::array<int, 3> &terminal) {
        Counts count{}, holes{};
        Mask empty = 0, blocked = 0;
        single = 0;
        for (int j = 0; j < slots; ++j) {
            count[j] = 2 * sizes[j];
            if (!sizes[j])
                empty |= flag(j);
            if (sizes[j] == 1)
                single |= flag(j);
            holes[j] = 13;
            for (int k = 0; k < 5; ++k) {
                int c = (j + k) % slots;
                holes[j] -= 2 * sizes[c] + std::count(terminal.begin(), terminal.end(), c);
            }
            if (holes[j] < 0)
                return false;
            if (!holes[j])
                blocked |= flag(j);
        }
        Domains domains;
        for (int v = 0; v < vertices; ++v) {
            choices[v].clear();
            Mask mark = 0;
            for (int k = 0; k < 3; ++k)
                if (roots[k] == v)
                    mark = flag(terminal[k]);
            for (auto row : all) {
                if ((row.colours & mark) != mark || (row.holes & blocked))
                    continue;
                row.colours ^= mark;
                if (row.colours & empty)
                    continue;
                domains[v].push_back(choices[v].size());
                choices[v].push_back(row);
            }
        }
        return visit(domains, (1 << vertices) - 1, count, holes);
    }
};
int main(int argc, char **argv) {
    if (argc != 3)
        throw std::runtime_error("arguments: core and schedule files");
    Search s;
    std::ifstream graph(argv[1]), schedule(argv[2]);
    int ignored;
    graph >> ignored;
    for (int &r : s.roots)
        graph >> r;
    int v, w;
    while (graph >> v >> w) {
        s.edges.emplace_back(v, w);
        s.adjacent[v][w] = s.adjacent[w][v] = true;
    }
    if (s.edges.size() != 57)
        throw std::runtime_error("wrong core");
    std::vector<Counts> schedules;
    int i, j, k;
    while (schedule >> i >> j >> k) {
        Counts row;
        for (int &n : row)
            schedule >> n;
        schedules.push_back(row);
    }
    int id, cases = 0, feasible = 0;
    std::array<int, 3> terminal;
    while (std::cin >> id >> terminal[0] >> terminal[1] >> terminal[2]) {
        if (s.solve(schedules.at(id), terminal)) {
            std::cout << "SAT " << id << " " << terminal[0] << " " << terminal[1] << " "
                      << terminal[2] << std::endl;
            ++feasible;
        }
        if (++cases % 1000 == 0)
            std::cerr << "checked " << cases << std::endl;
    }
    std::cout << "checked " << cases << " feasible " << feasible << " leaves " << s.complete
              << std::endl;
}
