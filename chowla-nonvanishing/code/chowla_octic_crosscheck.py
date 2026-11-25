"""Recompute the 13 new profiles' mutual and inherited Gram entries by partitions."""

from collections import Counter
from functools import cache
from itertools import product
from math import comb, prod

import chowla_octic_certificate as certificate


contractions = certificate.prior.quintic


@cache
def subsets(widths):
    """Submultisets, their complements, and their labelled multiplicities."""
    groups = tuple(Counter(widths).items())
    choices = []
    for sizes in product(*(range(count + 1) for _, count in groups)):
        selected = []
        remaining = []
        for (width, count), size in zip(groups, sizes):
            selected.extend([width] * size)
            remaining.extend([width] * (count - size))
        ways = prod(comb(count, size) for (_, count), size in zip(groups, sizes))
        choices.append((tuple(selected), tuple(remaining), ways))
    return choices


@cache
def ordinary_cumulant(widths):
    if len(widths) == 2:
        return 2 * min(widths)**2 - max(0, sum(widths) - 1)**2
    if sum(widths) <= 1:
        return 0
    return contractions.cubic.base.rect(widths)


@cache
def ordinary_partitions(left, right):
    """Group terms by the ordinary block containing the first left label."""
    if not left or not right:
        return int(not left and not right)
    first = left[0]
    value = 0
    for a, other_left, left_ways in subsets(left[1:]):
        for b, other_right, right_ways in subsets(right):
            if not b:
                continue
            weight = ordinary_cumulant(tuple(sorted((first,) + a + b)))
            if weight:
                value += left_ways * right_ways * weight * ordinary_partitions(
                    other_left, other_right
                )
    return value


def partition_inner(first_row, second_row):
    """First choose the labels in the unique marked block."""
    left, left_profile, _ = first_row
    right, right_profile, _ = second_row
    marked_weights = Counter()
    for a, remaining_left, left_ways in subsets(left):
        for b, remaining_right, right_ways in subsets(right):
            ways = left_ways * right_ways * ordinary_partitions(
                remaining_left, remaining_right
            )
            if ways:
                marked_weights[tuple(sorted(a + b))] += ways
    profile = contractions.cubic.moments.convolution(left_profile, right_profile)
    return sum(
        ways * contractions.cubic.marked_cumulant(profile, widths)
        for widths, ways in marked_weights.items()
    )


def profile_row(widths, order):
    legendre = [0] * (order // 2 - 1) + [1]
    return contractions.quart.profile_row(widths, legendre)


if __name__ == "__main__":
    previous = [
        profile_row((width,) * degree, order)
        for degree, width, order, _ in certificate.prior.PROFILES
    ]
    new = [profile_row(widths, order) for widths, order, _ in certificate.PROFILES]
    checked = 0
    for index, left in enumerate(new):
        for right in previous + new[:index + 1]:
            assert partition_inner(left, right) == contractions.inner(left, right)
            checked += 1
    print(f"Verified {checked} Gram entries by labelled cumulant partitions.")
