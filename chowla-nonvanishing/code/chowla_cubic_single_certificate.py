"""Exact rational test of the cubic refinement for quadratic central values.

The base witness and its previously certified lower gain are taken from the
accompanying 640-width certificate. Run this file with Python 3.
"""

from collections import defaultdict
from fractions import Fraction
from functools import cache

import chowla_grid160_certificate as base
import chowla_joint_certificate as splines
import chowla_quadratic_certificate as cumulants
import chowla_subgrid_single_certificate as subgrid

moments = subgrid.moments
BASE_GAIN = Fraction("0.00258410979460")
COT_UPPER = Fraction("3.916317365")

# Width numerators have denominator 160. Profiles use P2, P4 and P6.
CUBIC_ROWS = [
    ((16, 16, 16), [Fraction(-843632985, 1024), Fraction(4527783555, 2048), Fraction(-1382901975, 1024)]),
    ((24, 24, 24), [Fraction(-2156795735, 4096), Fraction(3256426715, 2048), Fraction(-2836411325, 4096)]),
    ((28, 28, 28), [Fraction(150750809, 256), Fraction(185921351, 256), Fraction(-54735791, 128)]),
    ((32, 32, 32), [Fraction(1709829173, 4096), Fraction(2969684575, 4096), Fraction(-76174163, 512)]),
    ((36, 36, 36), [Fraction(282792425, 512), Fraction(3214325, 16), Fraction(75487905, 512)]),
    ((40, 40, 40), [Fraction(90726253, 256), Fraction(54642395, 1024), Fraction(-38032237, 512)]),
    ((44, 44, 44), [Fraction(694679571, 4096), Fraction(-8283357, 512), Fraction(-88300827, 2048)]),
    ((48, 48, 48), [Fraction(10795455, 256), Fraction(-230175, 512), Fraction(4070385, 512)]),
    ((16, 20, 84), [Fraction(-260794455, 512), Fraction(27361435, 512), Fraction(-921335, 16)]),
    ((16, 32, 80), [Fraction(-2148009149, 4096), Fraction(85191821, 2048), Fraction(230378291, 4096)]),
    ((8, 20, 92), [Fraction(-1150920225, 1024), Fraction(342556025, 512), Fraction(-222565425, 1024)]),
    ((12, 32, 88), [Fraction(-300094123, 4096), Fraction(500910361, 4096), Fraction(-133210399, 2048)]),
    ((24, 40, 64), [Fraction(287061755, 2048), Fraction(334905713, 2048), Fraction(-5247569, 512)]),
    ((24, 32, 56), [Fraction(4299524187, 4096), Fraction(947160299, 4096), Fraction(-462839355, 2048)]),
]
CERTIFIED_PROPORTION = Fraction("0.945321516147")


@cache
def partitions(n):
    if n == 0:
        return ((),)
    result = []
    for partition in partitions(n - 1):
        result.append(partition + ((n - 1,),))
        for i, block in enumerate(partition):
            result.append(partition[:i] + (block + (n - 1,),) + partition[i + 1:])
    return tuple(result)


@cache
def mixed_partitions(left_count, right_count):
    # The marked factor has index zero. Every block without it must
    # connect the two normal-ordered products.
    return tuple(partition for partition in partitions(1 + left_count + right_count)
                 if all(0 in block or min(block) <= left_count < max(block)
                        for block in partition))


@cache
def contraction(left, right):
    widths = (0,) + left + right
    result = defaultdict(Fraction)
    for partition in mixed_partitions(len(left), len(right)):
        coefficient = 1
        for block in partition:
            group = tuple(sorted(widths[i] for i in block if i))
            if 0 in block:
                remaining = group
            elif len(block) == 2:
                coefficient *= base.cov(*group)
            elif sum(group) <= 1:
                coefficient = 0
                break
            else:
                coefficient *= base.rect(group)
        if coefficient:
            result[remaining] += coefficient
    return result


def marked_cumulant(profile, widths):
    if not widths:
        return splines.mean(profile)
    if len(widths) == 1:
        return splines.covariance(profile, widths[0])
    return cumulants.cumulant(profile, widths)


def inner_product(left, right):
    a, first, _ = left
    b, second, _ = right
    profile = moments.convolution(first, second)
    return sum(weight * marked_cumulant(profile, group)
               for group, weight in contraction(a, b).items())


def certify():
    assert subgrid.GRID == 640
    old = [((width,) if width else (), profile, size)
           for width, profile, size in subgrid.linear]
    old.extend(((a, b), profile, size) for a, b, profile, size in subgrid.pairs)
    central = moments.integer_spline(splines.approximate_H())
    lower, upper = moments.central_bounds(central, subgrid.linear, subgrid.pairs)
    assert lower > 0
    base_norm_upper = upper**2 / (2 * BASE_GAIN)
    cubic = []
    for numerators, coefficients in CUBIC_ROWS:
        widths = tuple(Fraction(numerator, 160) for numerator in numerators)
        radius = 1 - sum(widths)
        assert radius > 0
        profile = moments.integer_spline(splines.legendre_test(coefficients, radius))
        coefficient_size = sum(map(abs, coefficients))
        cubic.append((widths, profile, coefficient_size))
        inner = marked_cumulant(moments.convolution(central, profile), widths)
        a, b, c = widths
        error = 256 * radius * a * b * c * coefficient_size * Fraction(1, 10**12)
        lower += inner - error

    cross = sum(inner_product(row, original) for row in cubic for original in old)
    norm = sum((1 if i == k else 2) * inner_product(row, other)
               for i, row in enumerate(cubic) for k, other in enumerate(cubic[:i + 1]))
    norm_upper = base_norm_upper + 2 * cross + norm
    assert lower > 0 and norm_upper > 0
    return (19 - COT_UPPER) / 16 + lower**2 / (2 * norm_upper)


if __name__ == "__main__":
    value = certify()
    assert value > CERTIFIED_PROPORTION
    print("Certified lower nonvanishing proportion above", float(CERTIFIED_PROPORTION))
