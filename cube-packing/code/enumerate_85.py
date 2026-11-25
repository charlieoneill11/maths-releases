"""Enumerate the six full-plane patterns for an odd torus side congruent to 5 modulo 8.

    python3 enumerate_85.py --output /tmp/cube85-six.bin

Orbit records have fifteen unsigned fields, one byte per field through side 255
and two big-endian bytes beyond it. The first three are
the nonzero full levels, in axis order. For each axis, the next four fields give
(slope, intercept) at zero, followed by (slope, intercept) at its other level.
Each line is expressed as v = slope*u + intercept, with u<v in axis order.
"""

import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations, product
from math import gcd, isqrt, lcm
from struct import Struct

WIDE_RECORD = Struct('>15H')

@dataclass
class Domain:
    side: int
    steps: tuple
    inverse: dict
    distances: tuple
    hole_offsets: tuple


def domain_for(side):
    m = (side - 1) // 4
    steps = tuple(sign * 2 * d for d in range(1, m + 1) if m % d == 0
                  for sign in (1, -1))
    inverse = {s % side: pow(s, -1, side) for s in steps}
    coefficient_gcds = {gcd(side, 1 + a*b*c) for a, b, c in product(steps, repeat=3)}
    modulus = side // lcm(*coefficient_gcds)
    # Lemma 12 puts full levels and matching transverse hole coordinates
    # in one residue class modulo this common divisor of their differences.
    distances = tuple(range(modulus, side // 2 + 1, modulus))
    offsets = tuple(range(modulus, side, modulus))
    return Domain(side, steps, inverse, distances, offsets)


AXES = (0, 1, 2)
COORDS = ((1, 2), (0, 2), (0, 1))


def second_planes(domain, a, b, c, h):
    """Candidates meeting both perpendicular planes through the origin."""
    side, inverse = domain.side, domain.inverse
    inverse_a, inverse_b, inverse_c = (inverse[s % side] for s in (a, b, c))
    d = -h * inverse_a % side
    xs, ys, zs = [], [], []
    for t in domain.distances:
        x_intercept = (b * t + h) % side
        y_intercept = (a * t + h) % side
        z_intercept = (t - h) * inverse_a % side
        for slope in domain.steps:
            if (slope * (c * t + d) + x_intercept) % side == 0:
                xs.append((t, slope, x_intercept))
            if (slope * inverse_c * (t - d) + y_intercept) % side == 0:
                ys.append((t, slope, y_intercept))
            if (slope * inverse_b * (t - h) + z_intercept) % side == 0:
                zs.append((t, slope, z_intercept))
    return xs, ys, zs


def labeled_patterns(domain):
    side, inverse = domain.side, domain.inverse
    for a, b, c in product(domain.steps, repeat=3):
        for h in domain.hole_offsets:
            if h * (b + a * c) % side:
                continue
            first = ((a, h), (b, h), (c, -h * inverse[a % side] % side))
            xs, ys, zs = second_planes(domain, a, b, c, h)
            for x, sx, dx in xs:
                for y, sy, dy in ys:
                    if x > y or (sx * y + dx - sy * x - dy) % side:
                        continue
                    for z, sz, dz in zs:
                        if y > z:
                            continue
                        if (sx * (sz * x + dz) + dx - z) % side:
                            continue
                        if (sz * (z - dy) * inverse[sy % side] + dz - y) % side:
                            continue
                        second = ((sx, dx), (sy, dy), (sz, dz))
                        yield (x, y, z), tuple(zip(first, second))


def homogeneous_patterns(domain):
    """Pairs of class-one full planes with the same slope on each axis."""
    n = domain.side
    long_slope = (n - 1) // 2
    slopes = (2, -2, long_slope, -long_slope)
    for a, b, c in product(slopes, repeat=3):
        order = n // gcd(b + a*c, n)
        for h in range(order, n, order):
            inv_a = domain.inverse[a % n]
            first = ((a, h), (b, h), (c, -h*inv_a % n))
            for x in range(order, n//2 + 1, order):
                for y in range(x, n//2 + 1, order):
                    for z in range(y, n//2 + 1, order):
                        second = ((a, (b*x+h) % n), (b, (a*y+h) % n), (c, (z-h)*inv_a % n))
                        yield (x, y, z), tuple(zip(first, second))


@lru_cache(None)
def changes_of_coordinates(levels):
    """Axis permutations and reflections preserving the sorted distance triple."""
    transforms = []
    for perm in permutations(AXES):
        if tuple(levels[i] for i in perm) != levels:
            continue
        for signs in product((1, -1), repeat=3):
            shifts = tuple(t if s < 0 else 0 for t, s in zip(levels, signs))
            transforms.append((perm, signs, shifts))
    return transforms


def canonical(domain, levels, planes):
    side, inverse = domain.side, domain.inverse
    candidates = []
    for perm, signs, shifts in changes_of_coordinates(levels):
        entries = list(levels)
        for i, old_axis in enumerate(perm):
            u, v = COORDS[i]
            pair = planes[old_axis]
            if signs[i] < 0:
                pair = reversed(pair)
            for slope, intercept in pair:
                if perm[u] != COORDS[old_axis][0]:
                    slope = inverse[slope % side]
                    intercept = -slope * intercept
                slope = signs[v] * signs[u] * slope % side
                intercept = (signs[v] * intercept + shifts[v] - slope * shifts[u]) % side
                entries.extend((slope, intercept))
        candidates.append(bytes(entries) if side <= 255 else WIDE_RECORD.pack(*entries))
    return min(candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--side', type=int, default=85, help='odd torus side congruent to 5 modulo 8')
    parser.add_argument('--output', help='write the sorted canonical records to this file')
    parser.add_argument('--homogeneous', action='store_true',
                        help='restrict to the three class-one intervals in the cutoff proof')
    options = parser.parse_args()
    if not (5 <= options.side <= 65535 and options.side % 8 == 5):
        parser.error('the record format requires a side from 5 to 65535, congruent to 5 mod 8')
    domain = domain_for(options.side)
    primes = tuple(p for p in range(3, options.side + 1, 2)
                   if options.side % p == 0 and all(p % q for q in range(3, isqrt(p)+1, 2)))
    fibers = Counter()
    patterns = set()
    generate = homogeneous_patterns if options.homogeneous else labeled_patterns
    for levels, planes in generate(domain):
        coords = (*levels, *(c for pair in planes for _, c in pair))
        fibers[tuple(p for p in primes if all(t % p == 0 for t in coords))] += 1
        patterns.add(canonical(domain, levels, planes))
    if options.homogeneous:
        expected = {261: (1328, 114), 301: (480, 38)}
        if options.side in expected:
            assert (sum(fibers.values()), len(patterns)) == expected[options.side]
    elif options.side == 85:
        assert fibers == {(5,): 46088, (17,): 16640} and len(patterns) == 5558
    elif options.side == 133:
        assert fibers == {(7,): 71289, (19,): 21817} and len(patterns) == 8844
    elif options.side == 141:
        assert fibers == {(47,): 36864} and len(patterns) == 1266
    if options.output:
        with open(options.output, 'wb') as output:
            output.write(b''.join(sorted(patterns)))
    print(f'{sum(fibers.values()):,} labeled patterns and {len(patterns):,} symmetry orbits.')


if __name__ == '__main__':
    main()
