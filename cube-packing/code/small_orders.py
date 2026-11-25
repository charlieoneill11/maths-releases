"""List every odd packing parameter m admitting a given coefficient order."""

import argparse
from functools import lru_cache
from itertools import combinations_with_replacement
from math import gcd, isqrt, lcm


@lru_cache(maxsize=4096)
def divisors(n):
    low, high = [], []
    for i in range(1, isqrt(n) + 1):
        if n % i == 0:
            low.append(i)
            if i * i != n:
                high.append(n // i)
    return tuple(low + high[::-1])


def parameters(order):
    if order <= 0:
        raise ValueError('the additive order must be positive')
    if order % 2 == 0:
        return set()
    result = set()

    def record(side, roots, sign):
        if side % 8 != 5:
            return
        m = (side - 1) // 4
        a, b, c = roots
        if m % lcm(a, b, c) == 0 and side // gcd(side, 8 * a * b * c - sign) == order:
            result.add(m)

    # Either the original or complementary triple may have the small lcm.
    for multiple in range(1, 2 * order + 1, 2):
        for a, b, c in combinations_with_replacement(divisors(multiple), 3):
            if lcm(a, b, c) != multiple:
                continue
            for sign in (-1, 1):
                for side in divisors(order * (8 * a * b * c - sign)):
                    record(side, (a, b, c), sign)

    # Both lcms exceed 2q, so H*r*r' < 16*q^2 and r,r' are positive, 4 mod 8.
    for h in range(1, order**2, 2):
        if gcd(h, order) != 1:
            continue
        triples = {}
        for u, v, w in combinations_with_replacement(divisors(h), 3):
            if gcd(u, v, w) == 1 and lcm(u, v, w) == h:
                triples[u * v * w] = (u, v, w)
        for r in range(4, (4 * order**2 - 1) // h + 1, 8):
            for product, roots in triples.items():
                # k = r*H*E - sign*q divides this nonzero resultant.
                resultant = abs(8 * order**3 * product - (r * h)**3)
                for k in divisors(resultant):
                    for sign in (-1, 1):
                        e, rem = divmod(k + sign * order, r * h)
                        if rem or e <= 0 or e % 2 == 0 or e * h <= 2 * order:
                            continue
                        side, rem = divmod(order * (8 * e**3 * product - sign), k)
                        if rem == 0:
                            record(side, tuple(e * t for t in roots), sign)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('order', type=int, nargs='+')
    for q in parser.parse_args().order:
        matches = sorted(parameters(q))
        print(f'q={q}: {len(matches)} parameters; m={matches}')
