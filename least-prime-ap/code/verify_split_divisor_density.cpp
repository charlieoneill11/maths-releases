// Build with c++ -O3 -std=c++17. All probabilities use directed integer rounding.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using Wide = std::int64_t;
using Interval = std::pair<int, int>;
using Intervals = std::vector<Interval>;
constexpr int unit = 1'000'000;

enum class Bound { lower, upper };

int quotient(Wide numerator, Wide denominator, Bound bound) {
    return static_cast<int>((numerator + (bound == Bound::upper ? denominator - 1 : 0))
                            / denominator);
}

Intervals merge_intervals(Intervals intervals) {
    std::sort(intervals.begin(), intervals.end());
    Intervals merged;
    for (auto [low, high] : intervals) {
        if (merged.empty() || low > merged.back().second)
            merged.emplace_back(low, high);
        else
            merged.back().second = std::max(merged.back().second, high);
    }
    return merged;
}

// On a gap between target intervals the first residual has size r.
// The last split gives an available length g(r), affine between the indicated cuts.
Wide final_gap(const Intervals& targets, int start, int end, Bound bound) {
    if (start == end || start < targets.front().second) return 0;
    Intervals below;
    for (const auto& interval : targets) {
        if (interval.second > start) break;
        below.push_back(interval);
    }

    std::vector<int> cuts{start, end};
    auto add_cut = [&](int cut) {
        if (start < cut && cut < end) cuts.push_back(cut);
    };
    if (bound == Bound::lower) {
        for (auto [l1, u1] : below)
            for (auto [l2, u2] : below)
                for (int cut : {l1 + l2, l1 + u2, u1 + l2, u1 + u2}) add_cut(cut);
    } else {
        add_cut(below.front().first + below.back().second);
    }
    std::sort(cuts.begin(), cuts.end());
    cuts.erase(std::unique(cuts.begin(), cuts.end()), cuts.end());

    auto available_length = [&](int r) {
        if (bound == Bound::upper)
            return std::max(r - below.front().first, below.back().second);
        int length = 0;
        for (auto [low, high] : below) length += 2 * (high - low);
        for (auto [l1, u1] : below)
            for (auto [l2, u2] : below)
                length -= std::max(0, std::min(u1, r - l2) - std::max(l1, r - u2));
        return length;
    };

    Wide integral = 0;
    int left = start, g_left = available_length(left);
    for (std::size_t i = 1; i < cuts.size(); ++i) {
        const int right = cuts[i], g_right = available_length(right);
        const bool convex = Wide(g_left) * right >= Wide(g_right) * left;
        int probability;
        if (convex == (bound == Bound::lower)) {
            // The midpoint value of g(r)/r.
            probability = quotient(Wide(g_left + g_right) * unit, left + right, bound);
        } else {
            const int p_left = quotient(Wide(g_left) * unit, left, bound);
            const int p_right = quotient(Wide(g_right) * unit, right, bound);
            probability = quotient(p_left + p_right, 2, bound);
        }
        integral += Wide(right - left) * probability;
        left = right;
        g_left = g_right;
    }
    return integral;
}

int probability_bound(const Intervals& targets, int splits, Bound bound,
                      const std::array<int, 7>& bins) {
    if (targets.empty()) return 0;
    if (targets.front().first == 0) return unit;
    Wide integral = 0;
    int previous = 0;
    auto integrate_gap = [&](int start, int end) {
        if (start == end || end <= targets.front().first) return;
        if (splits == 2) {
            integral += final_gap(targets, start, end, bound);
            return;
        }
        const int step = (unit + bins[splits] - 1) / bins[splits];
        for (int left = start; left < end; left += step) {
            const int right = std::min(left + step, end);
            Intervals next;
            for (auto [low, high] : targets) {
                if (high > left) break;
                const int v = bound == Bound::lower
                    ? quotient(Wide(low) * unit, left, Bound::upper)
                    : quotient(Wide(low) * unit, right, Bound::lower);
                const int w = bound == Bound::lower
                    ? quotient(Wide(high) * unit, right, Bound::lower)
                    : quotient(Wide(high) * unit, left, Bound::upper);
                if (v < w || (bound == Bound::upper && v == w)) {
                    next.emplace_back(v, w);
                    next.emplace_back(unit - w, unit - v);
                }
            }
            integral += Wide(right - left)
                * probability_bound(merge_intervals(std::move(next)), splits - 1, bound, bins);
        }
    };
    for (auto [low, high] : targets) {
        integrate_gap(previous, low);
        integral += Wide(high - low) * unit;
        previous = high;
    }
    integrate_gap(previous, unit);
    return quotient(integral, unit, bound);
}

int main() {
    const Intervals inside{{142858, 199999}, {800001, 857142}};
    const Intervals outside{{142857, 200000}, {800000, 857143}};
    const int lower = probability_bound(inside, 6, Bound::lower, {0, 0, 0, 100, 220, 320, 450});
    const int upper = probability_bound(outside, 5, Bound::upper, {0, 0, 0, 400, 500, 600, 0});
    std::cout << "lower " << lower << "/" << unit << "\nupper " << upper << "/" << unit << '\n';
    // Exit status 0 only if the bounds stated in the paper hold: lower >= 0.587142, upper <= 0.595573.
    const bool ok = lower >= 587142 && upper <= 595573;
    std::cout << (ok ? "PASS" : "FAIL") << '\n';
    return ok ? 0 : 1;
}
