"""Verify the quartic refinement of the quadratic nonvanishing bound.

Run with Python 3 in the directory containing the earlier cubic certificate
and its dependencies. All comparisons and spline integrations use fractions.
"""

from fractions import Fraction
from math import prod
import sys

import chowla_cubic_single_certificate as cubic


# Width numerator on the 160 grid, followed by coefficients of P2 and P4.
QUARTIC_ROWS = [
    (16, [-510386, -291874]),
    (20, [-1974752, 1240532]),
    (24, [1295990, -2402543]),
    (28, [2797966, -473911]),
    (32, [1264735, 124269]),
    (36, [211240, -41256]),
]
BASE_PROPORTION = Fraction("0.945321516147")
CERTIFIED_PROPORTION = Fraction("0.945325433280444")


def profile_row(numerators, coefficients):
    widths = tuple(Fraction(i, 160) for i in numerators)
    radius = 1 - sum(widths)
    assert radius > 0
    spline = cubic.splines.legendre_test(coefficients, radius)
    return widths, cubic.moments.integer_spline(spline), sum(map(abs, coefficients))


def central_enclosure(central, row):
    widths, profile, weight = row
    joint_order = len(widths) + 1
    assert joint_order >= 3
    integral = cubic.marked_cumulant(cubic.moments.convolution(central, profile), widths)
    # Uniform Fourier error 10^-12 on [-1,1], Young's inequality, and
    # the L1 bound 2^(joint_order-1) for the restricted joint cumulant.
    amplitude_norm = 2 * (1 - sum(widths)) * weight
    cutoff_norms = prod(2 * width for width in widths)
    error = Fraction(2, 10**12) * amplitude_norm * cutoff_norms * 2**(joint_order - 1)
    return integral - error, integral + error


def certify():
    assert cubic.CERTIFIED_PROPORTION == BASE_PROPORTION
    subgrid = cubic.subgrid
    one_level = (19 - cubic.COT_UPPER) / 16
    central = cubic.moments.integer_spline(cubic.splines.approximate_H())
    lower, upper = cubic.moments.central_bounds(central, subgrid.linear, subgrid.pairs)
    old = [((width,) if width else (), profile, size) for width, profile, size in subgrid.linear]
    old.extend(((a, b), profile, size) for a, b, profile, size in subgrid.pairs)
    for widths, coefficients in cubic.CUBIC_ROWS:
        row = profile_row(widths, coefficients)
        old.append(row)
        left, right = central_enclosure(central, row)
        lower += left
        upper += right
    assert upper >= lower > 0
    # The cubic certificate proves its gain relative to this same rational
    # lower enclosure of the one-level bound.
    norm_upper = upper**2 / (2 * (BASE_PROPORTION - one_level))
    extra = [profile_row((width,) * 4, coefficients) for width, coefficients in QUARTIC_ROWS]
    for i, row in enumerate(extra):
        left, _ = central_enclosure(central, row)
        lower += left
        norm_upper += 2 * sum(cubic.inner_product(row, other) for other in old)
        norm_upper += cubic.inner_product(row, row)
        norm_upper += 2 * sum(cubic.inner_product(row, other) for other in extra[:i])
    assert lower > 0 and norm_upper > 0
    return one_level + lower**2 / (2 * norm_upper)


if __name__ == "__main__":
    result = certify()
    assert CERTIFIED_PROPORTION < result < CERTIFIED_PROPORTION + Fraction(1, 10**15)
    print("Verified lower proportion above 0.945325433280444.")
    margin = result - CERTIFIED_PROPORTION
    scaled = margin * 10**40
    lower = scaled.numerator // scaled.denominator
    assert lower < scaled < lower + 1
    print(f"Margin lies strictly between {lower} and {lower + 1} times 10^-40.")
    if "--exact-margin" in sys.argv[1:]:
        print(f"Exact margin in hexadecimal: {margin.numerator:#x}/{margin.denominator:#x}")
