#include <algorithm>
#include <array>
#include <iostream>
#include <stdexcept>
#include <vector>

using Grid = std::vector<int>;

constexpr int prime = 19;
constexpr int m = prime * prime;
constexpr int length = 4 * m + 1;
constexpr int slope = 2 * prime;
constexpr int required = (m - 1) * length / 2 + 1;

int residue(int value, int modulus) {
    int result = value % modulus;
    return result < 0 ? result + modulus : result;
}

// Each signed slope is an even divisor, hence every step is a unit modulo the period.
void sum_intervals(Grid& input, Grid& output, int lines, int period, int step,
                   int width, int stride) {
    if (width == 1) return;
    for (int line = 0; line < lines; ++line) {
        const int start = stride == 1 ? line * period : line;
        int total = 0;
        for (int j = 0; j < width; ++j)
            total += input[start + residue(j * step, period) * stride];
        int current = 0;
        int next = residue(width * step, period);
        for (int j = 0; j < period; ++j) {
            output[start + current * stride] = total;
            total += input[start + next * stride] - input[start + current * stride];
            current = (current + step) % period;
            next = (next + step) % period;
        }
    }
    input.swap(output);
}

int overlap(int parent_length, int parent_slope) {
    const int a = std::abs(parent_slope) / 2;
    const int parent_m = (parent_length - 1) / 4;
    Grid counts(length * parent_length), scratch(counts.size());
    for (int x = 0; x < parent_length; ++x)
        for (int y = 0; y < parent_length; ++y) {
            const int base = residue(y - slope * x, length);
            const int parent = residue(y - parent_slope * x, parent_length);
            ++counts[base * parent_length + parent];
        }
    sum_intervals(counts, scratch, length, parent_length, 2, a, 1);
    sum_intervals(counts, scratch, length, parent_length, 4 * a, parent_m / a, 1);
    sum_intervals(counts, scratch, parent_length, length, 2, prime, parent_length);
    sum_intervals(counts, scratch, parent_length, length, 4 * prime, prime, parent_length);
    return *std::max_element(counts.begin(), counts.end());
}

int main() {
    const std::array<int, 3> expected{172902, 130325, 131541};
    for (int i = 0; i < 3; ++i) {
        const int parent_length = length + 4 * (i - 1);
        const int parent_m = (parent_length - 1) / 4;
        int maximum = 0;
        for (int a = 1; a <= parent_m; ++a) {
            if (parent_m % a) continue;
            for (int candidate : {-2 * a, 2 * a}) {
                if (parent_length == length && candidate == slope) continue;
                maximum = std::max(maximum, overlap(parent_length, candidate));
            }
        }
        int upper = maximum + 2 * parent_length * (prime + 4) + 10 * m;
        std::cout << "parent " << parent_length << ", raw " << maximum
                  << ", ordinary surgery upper bound " << upper << '\n';
        if (maximum != expected[i] || upper >= required)
            throw std::runtime_error("ordinary surgery certificate failed");
    }

    std::vector<bool> digit(length);
    for (int i = 0; i < prime; ++i)
        for (int j = 0; j < prime; ++j)
            digit[2 * i + 4 * prime * j] = true;
    for (int sign : {-1, 1}) {
        for (int gap : {1, 3}) {
            std::vector<bool> pair(length);
            for (int y = 0; y < length; ++y)
                pair[y] = digit[y] || digit[residue(y - sign * slope * gap, length)];
            int after_shift = 0;
            for (int y = 0; y < length; ++y)
                after_shift += pair[y] != pair[residue(y - 2, length)];
            int closest = length;
            for (int h = 0; h < length; ++h) {
                int difference = 0;
                for (int y = 0; y < length; ++y) {
                    int relative = residue(y - h, length);
                    difference += pair[y] != (relative != 0 && relative % 2 == 0);
                }
                closest = std::min(closest, difference);
            }
            std::cout << "signed gap " << sign * gap << ", shift difference "
                      << after_shift << ", minimum line difference " << closest << '\n';
            if ((gap == 1 && (after_shift != 2 || closest != 0)) ||
                (gap == 3 && (after_shift != 6 || closest != 38)))
                throw std::runtime_error("line certificate failed");
        }
    }

    int phase_maximum = 0;
    for (int displacement : {-2 * m, 2 * m})
        for (int seam : {-2 * slope, 0, 2 * slope})
            for (int r = -8; r <= 8; ++r) {
                const int phase = displacement + seam + 2 * r;
                int common = 0;
                for (int y = 0; y < length; ++y)
                    common += digit[y] && digit[residue(y - phase, length)];
                phase_maximum = std::max(phase_maximum, common);
            }
    int upper = length * phase_maximum + 2 * length * (prime + 4) + 10 * m;
    std::cout << "matching slope, permitted digit overlap " << phase_maximum
              << ", ordinary surgery upper bound " << upper << '\n';
    if (phase_maximum != 88 || upper >= required)
        throw std::runtime_error("matching slope certificate failed");
}
