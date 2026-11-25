#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

namespace {
using Integer = std::int64_t;
constexpr std::array block_lengths{8, 12, 16, 20, 24, 30, 36, 42, 48, 56,
                                   64, 72, 84, 96, 112, 128, 160, 192, 224, 256};

bool is_prime(int value) {
    if (value < 2) return false;
    for (int divisor = 2; divisor * divisor <= value; ++divisor) {
        if (value % divisor == 0) return false;
    }
    return true;
}

std::vector<int> divisors(int value) {
    std::vector<int> result;
    for (int divisor = 1; divisor <= value; ++divisor) {
        if (value % divisor == 0) result.push_back(divisor);
    }
    return result;
}

bool all_coefficients_are_units(int side, const std::vector<int>& factors) {
    for (int a : factors) for (int b : factors) for (int c : factors) {
        for (int sign : {-1, 1}) {
            if (std::gcd(8LL * a * b * c + sign, static_cast<long long>(side)) > 1) return false;
        }
    }
    return true;
}

bool class_one_is_possible(int side) {
    for (int index : {1, 3, 7, 9}) {
        if (side % index != 0) continue;
        const int order = side / index;
        const int arc_capacity = 1 + 90 / index;
        if (order <= 10 || order * order - 40 * order + 300 <= order * arc_capacity) return true;
    }
    return false;
}

int most_in_arc(const std::vector<int>& doubled_points, int count, int width) {
    int best = 0, end = 0;
    for (int start = 0; start < count; ++start) {
        while (end < start + count && doubled_points[end] - doubled_points[start] <= width) ++end;
        best = std::max(best, end - start);
    }
    return best;
}

bool excludes_transition(int side, int a, int first_parent, int b, int second_parent) {
    const int m = (side - 1) / 4;
    const int first_radius = first_parent == side ? 1 : 2;
    const int second_radius = second_parent == side ? 1 : 2;
    const int omitted = (first_parent < side ? 12 : 14) + (second_parent < side ? 12 : 14);
    const Integer parents = Integer(first_parent) * second_parent;
    const Integer denominator = side * parents;
    const Integer local = 2 * m * parents + Integer(side) *
        (first_radius * second_parent + second_radius * first_parent);
    const Integer global = local + 2 * Integer(side) *
        (std::abs(a) * first_radius * second_parent + std::abs(b) * second_radius * first_parent);
    const int repeat = std::gcd(std::abs(b - a), side);
    std::vector<int> forced(m);
    for (int d = 0; d < m; ++d) {
        const Integer arc_numerator = global + 2 * d * parents;
        const Integer capacity = repeat * (1 + side * arc_numerator / (denominator * repeat));
        forced[d] = side - static_cast<int>(std::min<Integer>(side, capacity));
    }
    const auto exceeds_budget = [&]() {
        int cost = 0;
        for (int number : forced) cost += std::max(0, number - omitted);
        return cost > side - 2;
    };
    if (exceeds_budget()) return true;

    const int period = std::lcm(first_parent, second_parent);
    int step = b * (period / second_parent) - a * (period / first_parent);
    step = (step % period + period) % period;
    for (int size : block_lengths) {
        if (size > side) continue;
        std::vector<int> points(2 * size);
        for (int i = 0; i < size; ++i) points[i] = (Integer(i) * step) % period;
        std::sort(points.begin(), points.begin() + size);
        for (int i = 0; i < size; ++i) points[size + i] = points[i] + period;
        for (int d = 0; d < m; ++d) {
            const Integer width = period * (local + 2 * d * parents) / denominator;
            if (width >= period) break;
            const int best = most_in_arc(points, size, static_cast<int>(width));
            // Each of at most five chart segments can have one incomplete block.
            const int capacity = best * (side + 5 * (size - best)) / size;
            forced[d] = std::max(forced[d], side - capacity);
        }
        if (exceeds_budget()) return true;
    }
    return false;
}
} // namespace

int main() {
    std::vector<int> remaining;
    int tested_sides = 0, tested_transitions = 0;
    for (int side = 5; side < 653; side += 8) {
        const int m = (side - 1) / 4;
        const auto factors = divisors(m);
        if (is_prime(side) || is_prime(m) || all_coefficients_are_units(side, factors)) continue;
        if (side == 85 || side == 133 || side == 141) continue;
        if (side < 173) {
            std::cerr << "Endpoint obstruction unavailable at unhandled side " << side << '\n';
            return 1;
        }
        int trials = 0;
        for (int a : factors) {
            if (a * a > m) break;
            for (int first : {side - 4, side, side + 4}) {
                if (((first - 1) / 4) % a != 0) continue;
                for (int second : {side - 4, side, side + 4}) {
                    for (int magnitude : divisors((second - 1) / 4)) for (int sign : {-1, 1}) {
                        const int b = sign * magnitude;
                        if (b == a) continue;
                        ++trials;
                        if (!excludes_transition(side, a, first, b, second)) {
                            std::cerr << "Unexcluded transition " << side << ' ' << a << ' ' << first
                                      << ' ' << b << ' ' << second << '\n';
                            return 1;
                        }
                    }
                }
            }
        }
        ++tested_sides;
        tested_transitions += trials;
        if (class_one_is_possible(side)) remaining.push_back(side);
        std::cout << side << ": excluded all " << trials << " transitions\n";
    }
    std::cout << tested_sides << " sides, " << tested_transitions << " transitions; class-one survivors";
    for (int side : remaining) std::cout << ' ' << side;
    std::cout << '\n';
    return remaining == std::vector<int>{261, 301} ? 0 : 1;
}
