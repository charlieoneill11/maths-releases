"""Exact products in Gardam's left Laurent normal form x^i y^j z^k r."""

from collections import Counter
from itertools import product

SIGNS = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
ZERO = (0, 0, 0)
CARRY = (
    (ZERO, ZERO, ZERO, ZERO),
    (ZERO, (1, 0, 0), ZERO, (1, 0, 0)),
    (ZERO, (-1, 1, -1), (0, 1, 0), (-1, 0, -1)),
    (ZERO, (0, -1, 1), (0, -1, 0), (0, 0, 1)),
)
OFFSETS = ((0, 0, 0), (1, 1, 0), (0, 1, 1), (1, 0, -1))
E = (0, 0, 0, 0)
ONE = {E: 1}
A, B = (0, 0, 0, 1), (0, 0, 0, 2)


def mul(g, h):
    i, j, k, r = g
    l, m, n, s = h
    a, b, c = CARRY[r][s]
    x, y, z = SIGNS[r]
    return i + x * l + a, j + y * m + b, k + z * n + c, r ^ s


def inverse(g):
    *v, r = g
    return (*(-s * (t + c) for s, t, c in zip(SIGNS[r], v, CARRY[r][r])), r)


def affine(g):
    i, j, k, r = g
    a, b, c = OFFSETS[r]
    return SIGNS[r], (2 * i + a, 2 * j + b, -2 * k + c)


def from_affine(pair):
    sign, t = pair
    r = SIGNS.index(tuple(sign))
    d = [x - y for x, y in zip(t, OFFSETS[r])]
    assert all(z % 2 == 0 for z in d)
    return d[0] // 2, d[1] // 2, -d[2] // 2, r


def ball(radius):
    seen = frontier = {E}
    for _ in range(radius):
        frontier = {
            mul(g, h) for g in frontier for h in (A, B, inverse(A), inverse(B))
        } - seen
        seen = seen | frontier
    return seen


def syllable(t, sign, m):
    if sign == 1:
        return 2 * abs(t)
    return 1 + 2 * min(abs(t - m), abs(t - m - 1))


def inverse_box(window):
    """Intersect nine necessary length bounds. Enumerate the full lattice box."""
    coordinates = [affine(g) for g in window]
    bounds = [
        [max(syllable(t[i], s[i], m) for s, t in coordinates) for m in (-1, 0, 1)]
        for i in range(3)
    ]
    result = set()
    for signs in SIGNS:
        axes = []
        for i, sign in enumerate(signs):
            # For m=0 the bound implies |t| <= 1 + M/2.
            limit = 1 + bounds[i][1] // 2
            parity = OFFSETS[SIGNS.index(signs)][i] % 2
            axes.append(
                [
                    t
                    for t in range(-limit, limit + 1)
                    if t % 2 == parity
                    and all(
                        syllable(t, sign, m) <= bound
                        for m, bound in zip((-1, 0, 1), bounds[i])
                    )
                ]
            )
        result.update(from_affine((signs, t)) for t in product(*axes))
    return result


def convolution(u, v):
    out = Counter()
    for g, a in u.items():
        for h, b in v.items():
            out[mul(g, h)] += a * b
    return {g: c for g, c in out.items() if c}


def reduce_mod(u, n):
    return {g: a % n for g, a in u.items() if a % n}


def indicator(points):
    return dict.fromkeys(points, 1)
