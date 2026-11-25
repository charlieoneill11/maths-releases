"""Exact rational verification of a marked one-character witness on a finer width grid.

Uses the integer rows and compact-support symplectic cumulants in the accompanying
160-grid and spectral-refinement certificates. Run with Python 3.
"""

from fractions import Fraction
from multiprocessing import Pool

import chowla_grid160_certificate as original
import chowla_joint_certificate as spline
import chowla_spectral_refinement_certificate as moments

SUBDIVISIONS = 4
GRID = 160 * SUBDIVISIONS
moments.GRID = GRID
ROUNDING_SCALE = 10**8


def linear_coefficients():
    old = [[0] * 7, *original.linear_rows, [0] * 7]
    rows = [[0] * 7 for _ in range(GRID + 1)]
    for i in range(1, 160):
        for column, coefficient in enumerate(old[i]):
            smooth = coefficient
            if i % 8 == 0:
                smooth = Fraction(old[i - 1][column] + old[i + 1][column], 2)
            center = SUBDIVISIONS * i
            rows[center][column] += coefficient
            for offset in range(1, SUBDIVISIONS):
                weight = Fraction(SUBDIVISIONS - offset, SUBDIVISIONS**2)
                increment = round(smooth * weight)
                rows[center][column] -= 2 * increment
                rows[center - offset][column] += increment
                rows[center + offset][column] += increment
    return rows[1:GRID]


linear = [moments.row(0, [-value for value in original.projection])]
linear += [moments.row(i, row) for i, row in enumerate(linear_coefficients(), 1)]
for index, extra in moments.ADDED.items():
    linear.append(moments.row(SUBDIVISIONS * index, [0] * 7 + extra))

pairs = []
for (i, j), coefficients in zip(original.pair_indices, original.quadratic_rows):
    a, b = Fraction(i, 40), Fraction(j, 40)
    profile = moments.integer_spline(spline.legendre_test(coefficients, 1 - a - b))
    pairs.append((a, b, profile, sum(map(abs, coefficients))))


def ceiling_scaled(value):
    numerator = value.numerator * ROUNDING_SCALE
    return -((-numerator) // value.denominator)


def linear_norm_row(i):
    row = linear[i]
    value = sum((1 if i == k else 2) * moments.linear_inner(row, other)
                for k, other in enumerate(linear[:i + 1]))
    value += 2 * sum(moments.quadratic_inner(row, other) for other in pairs)
    return ceiling_scaled(value)


def quadratic_norm_row(i):
    a, b, profile, _ = pairs[i]
    value = sum((1 if i == k else 2) * original.quadratic(
        moments.convolution(profile, other), a, b, c, d)
                for k, (c, d, other, _) in enumerate(pairs[:i + 1]))
    return ceiling_scaled(value)


if __name__ == "__main__":
    central = moments.integer_spline(spline.approximate_H())
    numerator, _ = moments.central_bounds(central, linear, pairs)
    with Pool(4) as workers:
        costs = workers.map(linear_norm_row, range(len(linear)))
        costs += workers.map(quadratic_norm_row, range(len(pairs)))
    norm_upper = Fraction(sum(costs), ROUNDING_SCALE)
    assert numerator > 0 and norm_upper > 0
    gain = numerator**2 / (2 * norm_upper)
    proportion = (19 - Fraction(3916317365, 10**9)) / 16 + gain
    assert proportion > Fraction("0.94531427448210")
    print("Certified nonvanishing lower proportion above 0.94531427448210.")
