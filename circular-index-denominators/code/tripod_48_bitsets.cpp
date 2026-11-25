#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
// Alternate exhaustive replay using precomputed palette compatibility bitsets.
using namespace std;
using Mask = uint64_t;
const Mask all_slots = (Mask(1) << 48) - 1;
Mask bit(int i) { return Mask(1) << i; }
int roots[3];
bool adjacent[13][13];
int class_sizes[48], deficit_positions[3], terminals[3], holes_needed[48], chosen[13];
long long leaves = 0;
struct Palette {
    Mask colours, holes, internal;
};
vector<Palette> all_palettes, vertex_choices[13];
Mask singletons, empty_slots;
void generate_palettes() {
    set<Mask> s;
    for (int a = 0; a < 9; a++)
        for (int b = a; b < 9; b++)
            for (int c = b; c < 9; c++) {
                Mask w = 0;
                int j = 0;
                for (int i = 0; i < 9; i++) {
                    w |= bit(j);
                    j += 5 + (a == i) + (b == i) + (c == i);
                }
                for (int k = 0; k < 48; k++) {
                    s.insert(w);
                    w = ((w << 1) & all_slots) | (w >> 47);
                }
            }
    for (Mask w : s) {
        Mask cov = 0;
        for (int k = 0; k < 5; k++)
            cov |= ((w >> k) | (w << (48 - k))) & all_slots;
        all_palettes.push_back({w, all_slots ^ cov, w});
    }
}
void initialize_domains() {
    singletons = empty_slots = 0;
    for (int i = 0; i < 48; i++) {
        if (class_sizes[i] == 1)
            singletons |= bit(i);
        if (!class_sizes[i])
            empty_slots |= bit(i);
        holes_needed[i] = 1;
    }
    for (int h : deficit_positions)
        holes_needed[h] += 2;
    for (int c : terminals)
        for (int k = 0; k < 5; k++)
            holes_needed[(c - k + 48) % 48]--;
    Mask holes = 0;
    for (int i = 0; i < 48; i++)
        if (holes_needed[i])
            holes |= bit(i);
    for (int v = 0; v < 13; v++) {
        vertex_choices[v].clear();
        Mask t = 0;
        for (int i = 0; i < 3; i++)
            if (roots[i] == v)
                t = bit(terminals[i]);
        for (auto p : all_palettes)
            if ((p.colours & t) == t && !(p.holes & ~holes) && !((p.colours ^ t) & empty_slots)) {
                p.internal = p.colours ^ t;
                vertex_choices[v].push_back(p);
            }
    }
}
vector<pair<int, int>> edges;
Mask unused_colours[13];
bool colour(uint64_t remaining) {
    if (!remaining)
        return true;
    int best = -1, minc = 50;
    Mask opt = 0;
    for (Mask m = remaining; m; m &= m - 1) {
        int e = countr_zero(m);
        auto [i, j] = edges[e];
        Mask opts = unused_colours[i] & unused_colours[j];
        int n = popcount(opts);
        if (!n)
            return false;
        if (n < minc)
            minc = n, best = e, opt = opts;
    }
    auto [i, j] = edges[best];
    for (; opt; opt &= opt - 1) {
        Mask h = opt & -opt;
        unused_colours[i] ^= h;
        unused_colours[j] ^= h;
        if (colour(remaining ^ bit(best)))
            return true;
        unused_colours[i] ^= h;
        unused_colours[j] ^= h;
    }
    return false;
}
// Fourteen 64-bit words cover all 880 possible star palettes.
constexpr int words = 14;
struct PaletteSet {
    Mask a[words]{};
    void set(int i) { a[i / 64] |= bit(i % 64); }
    int size() const {
        int s = 0;
        for (Mask w : a)
            s += popcount(w);
        return s;
    }
};
int vertex_type[13], word_count[4];
struct Tables {
    vector<Palette> choices;
    vector<array<array<PaletteSet, 2>, 4>> compatible;
    array<PaletteSet, 48> contains{}, holes{};
};
Tables tables[4];
struct Domains {
    PaletteSet d[13];
};
// The ordinary core vertices share a domain. Each terminal root has its own.
void build_compatibility_tables() {
    for (int i = 0; i < 13; i++)
        vertex_type[i] = 0;
    for (int i = 0; i < 3; i++)
        vertex_type[roots[i]] = i + 1;
    for (int k = 0; k < 4; k++) {
        auto &t = tables[k];
        int v = k ? roots[k - 1] : 0;
        if (!k)
            while (vertex_type[v])
                v++;
        t.choices = vertex_choices[v];
        t.compatible.assign(t.choices.size(), {});
        t.contains = {};
        t.holes = {};
        word_count[k] = (t.choices.size() + 63) / 64;
        for (int a = 0; a < int(t.choices.size()); a++) {
            auto p = t.choices[a];
            for (Mask m = p.internal; m; m &= m - 1)
                t.contains[countr_zero(m)].set(a);
            for (Mask m = p.holes; m; m &= m - 1)
                t.holes[countr_zero(m)].set(a);
        }
    }
    for (int k = 0; k < 4; k++)
        for (int r = k; r < 4; r++)
            for (int i = 0; i < int(tables[k].choices.size()); i++)
                for (int j = (k == r ? i : 0); j < int(tables[r].choices.size()); j++) {
                    auto a = tables[k].choices[i], b = tables[r].choices[j];
                    Mask sh = a.internal & b.internal, f = sh & singletons;
                    if (!f) {
                        tables[k].compatible[i][r][0].set(j);
                        tables[r].compatible[j][k][0].set(i);
                    }
                    if (sh && popcount(f) <= 1) {
                        tables[k].compatible[i][r][1].set(j);
                        tables[r].compatible[j][k][1].set(i);
                    }
                }
}
int endpoints_needed[48];
// Each of the two count families must lie between its forced and possible totals.
// Three passes are an optimization only. Remaining choices are searched exhaustively.
bool propagate(Domains &domains, int remaining_after_choice) {
    for (int pass = 0; pass < 3; pass++) {
        Mask possible_holes[13]{}, possible_colours[13]{}, forced_holes[13]{}, forced_colours[13]{};
        // Bit-sliced counters for the number of supporting remaining vertices.
        Mask u[2][4]{}, l[2][4]{};
        for (int i = 0; i < 13; i++)
            if (remaining_after_choice >> i & 1) {
                int k = vertex_type[i];
                Mask ah = 0, ac = 0, lh = all_slots, lc = all_slots;
                for (int z = 0; z < word_count[k]; z++)
                    for (Mask m = domains.d[i].a[z]; m; m &= m - 1) {
                        auto p = tables[k].choices[z * 64 + countr_zero(m)];
                        ah |= p.holes;
                        ac |= p.internal;
                        lh &= p.holes;
                        lc &= p.internal;
                    }
                possible_holes[i] = ah;
                possible_colours[i] = ac;
                forced_holes[i] = lh;
                forced_colours[i] = lc;
                Mask upper[2] = {ah, ac}, lower[2] = {lh, lc};
                for (int a = 0; a < 2; a++)
                    for (int j = 0; j < 4; j++) {
                        Mask next = upper[a] & u[a][j];
                        u[a][j] ^= upper[a];
                        upper[a] = next;
                        next = lower[a] & l[a][j];
                        l[a][j] ^= lower[a];
                        lower[a] = next;
                    }
            }
        Mask must_use[2]{}, must_omit[2]{};
        for (int a = 0; a < 2; a++)
            for (int c = 0; c < 48; c++) {
                int req = a ? endpoints_needed[c] : holes_needed[c];
                int hi = 0, lo = 0;
                for (int j = 0; j < 4; j++) {
                    hi += ((u[a][j] >> c) & 1) << j;
                    lo += ((l[a][j] >> c) & 1) << j;
                }
                if (hi < req || lo > req)
                    return false;
                if (hi == req)
                    must_use[a] |= bit(c);
                if (lo == req)
                    must_omit[a] |= bit(c);
            }
        bool changed = false;
        for (int i = 0; i < 13; i++)
            if (remaining_after_choice >> i & 1) {
                int k = vertex_type[i];
                Mask optional[2] = {possible_holes[i] ^ forced_holes[i],
                                    possible_colours[i] ^ forced_colours[i]};
                if (!((optional[0] & (must_use[0] | must_omit[0])) ||
                      (optional[1] & (must_use[1] | must_omit[1]))))
                    continue;
                Mask any = 0;
                for (int z = 0; z < word_count[k]; z++) {
                    Mask before = domains.d[i].a[z], res = before;
                    for (int a = 0; a < 2 && res; a++) {
                        for (Mask h = must_use[a] & optional[a]; h && res; h &= h - 1) {
                            int c = countr_zero(h);
                            res &= a ? tables[k].contains[c].a[z] : tables[k].holes[c].a[z];
                        }
                        for (Mask h = must_omit[a] & optional[a]; h && res; h &= h - 1) {
                            int c = countr_zero(h);
                            res &= ~(a ? tables[k].contains[c].a[z] : tables[k].holes[c].a[z]);
                        }
                    }
                    any |= res;
                    changed |= (before != res);
                    domains.d[i].a[z] = res;
                }
                if (!any)
                    return false;
            }
        if (!changed)
            break;
    }
    return true;
}
bool search_palettes(const Domains &domains, int remaining, Mask seen, Mask twice) {

    if (!remaining) {
        leaves++;
        for (int v = 0; v < 13; v++)
            unused_colours[v] = tables[vertex_type[v]].choices[chosen[v]].internal;
        return colour((Mask(1) << 57) - 1);
    }
    int v = -1, fewest = 10000;
    for (int i = 0; i < 13; i++)
        if (remaining >> i & 1) {
            int k = domains.d[i].size();
            if (k < fewest)
                fewest = k, v = i;
        }
    if (!fewest)
        return false;
    int remaining_after_choice = remaining ^ (1 << v), t = vertex_type[v];
    for (int zz = 0; zz < word_count[t]; zz++)
        for (Mask m = domains.d[v].a[zz]; m; m &= m - 1) {
            int a = 64 * zz + countr_zero(m);
            auto p = tables[t].choices[a];
            Mask filled_windows = 0;
            for (Mask h = p.holes; h; h &= h - 1) {
                int j = countr_zero(h);
                if (!--holes_needed[j])
                    filled_windows |= bit(j);
            }
            Mask filled_singletons = p.internal & seen & ~twice & singletons;
            Domains next_domains;
            bool ok = true;
            PaletteSet forbidden[4]{};
            for (int k = 0; k < 4; k++) {
                for (Mask m = filled_windows; m; m &= m - 1) {
                    auto &bs = tables[k].holes[countr_zero(m)];
                    for (int j = 0; j < word_count[k]; j++)
                        forbidden[k].a[j] |= bs.a[j];
                }
                for (Mask m = filled_singletons; m; m &= m - 1) {
                    auto &bs = tables[k].contains[countr_zero(m)];
                    for (int j = 0; j < word_count[k]; j++)
                        forbidden[k].a[j] |= bs.a[j];
                }
            }
            for (int i = 0; i < 13 && ok; i++)
                if (remaining_after_choice >> i & 1) {
                    int k = vertex_type[i];
                    auto &allow = tables[t].compatible[a][k][adjacent[v][i]];
                    Mask any = 0;
                    for (int j = 0; j < word_count[k]; j++) {
                        next_domains.d[i].a[j] =
                            domains.d[i].a[j] & allow.a[j] & ~forbidden[k].a[j];
                        any |= next_domains.d[i].a[j];
                    }
                    if (!any)
                        ok = false;
                }
            if (ok) {
                chosen[v] = a;
                // For each selected vertex the core edges to its selected neighbours must
                // have distinct colours. Singleton classes force their respective edges.
                for (int i = 0; i < 13 && ok; i++)
                    if (!(remaining_after_choice >> i & 1)) {
                        Mask force = 0;
                        for (int j = 0; j < 13; j++)
                            if (!(remaining_after_choice >> j & 1) && adjacent[i][j]) {
                                Mask w = tables[vertex_type[i]].choices[chosen[i]].internal &
                                         tables[vertex_type[j]].choices[chosen[j]].internal;
                                Mask f = w & singletons;
                                if (!f && has_single_bit(w))
                                    f = w;
                                if (f & force) {
                                    ok = false;
                                    break;
                                }
                                force |= f;
                            }
                    }
            }
            for (Mask w = p.internal; w; w &= w - 1)
                endpoints_needed[countr_zero(w)]--;
            if (ok && propagate(next_domains, remaining_after_choice) &&
                search_palettes(next_domains, remaining_after_choice, seen | p.internal,
                                twice | filled_singletons))
                return true;
            for (Mask w = p.internal; w; w &= w - 1)
                endpoints_needed[countr_zero(w)]++;
            for (Mask h = p.holes; h; h &= h - 1)
                holes_needed[countr_zero(h)]++;
        }
    return false;
}
int main(int argc, char **argv) {
    if (argc != 3)
        throw runtime_error("arguments: core and schedule files");
    ifstream core(argv[1]), schedules(argv[2]);
    int instance;
    if (!(core >> instance))
        throw runtime_error("could not read core");
    for (int &v : roots)
        core >> v;
    int u, v;
    while (core >> u >> v) {
        adjacent[u][v] = adjacent[v][u] = true;
        edges.emplace_back(u, v);
    }
    if (edges.size() != 57)
        throw runtime_error("wrong core");
    generate_palettes();
    vector<array<int, 51>> rows;
    array<int, 51> row;
    while (schedules >> row[0]) {
        for (int i = 1; i < 51; i++)
            schedules >> row[i];
        rows.push_back(row);
    }
    int cases = 0, feasible = 0, id;
    while (cin >> id >> terminals[0] >> terminals[1] >> terminals[2]) {
        auto &schedule = rows.at(id);
        copy_n(schedule.begin(), 3, deficit_positions);
        copy_n(schedule.begin() + 3, 48, class_sizes);
        initialize_domains();
        build_compatibility_tables();
        Domains domains;
        for (int i = 0; i < 13; i++) {
            for (int j = 0; j < int(tables[vertex_type[i]].choices.size()); j++)
                domains.d[i].set(j);
        }
        for (int j = 0; j < 48; j++)
            endpoints_needed[j] = 2 * class_sizes[j];
        if (search_palettes(domains, (1 << 13) - 1, 0, 0)) {
            cout << "SAT " << id << " " << terminals[0] << " " << terminals[1] << " "
                 << terminals[2] << endl;
            ++feasible;
        }
        ++cases;
    }
    cout << "checked " << cases << " feasible " << feasible << " leaves " << leaves << endl;
}
