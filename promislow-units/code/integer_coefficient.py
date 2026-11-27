"""Decode an individual ordinary integer coefficient of either factored word.

Work in a chosen Laurent-series expansion of the known integral quotient.
Suffix displacement bounds prune numerator paths that cannot contribute.
Cost depends on the chosen site. The default checks the four published
coefficients by direct coefficient summation.
"""

import argparse
from collections import Counter
from functools import cache, reduce
from itertools import groupby

from integral_unit import DATA, ONE, mul, vertex
from verify import AA, BB, IDENT, REPS, TRANSLATIONS, compose, power


@cache
def terms(j):
    m, _, k = DATA["vertices"][abs(j) - 1]
    return {(i, n * k, e): c for (i, n, e), c in vertex(m, j < 0).items()}


def multiply_key(left, right):
    s, t = left
    u, v = right
    return tuple(a * b for a, b in zip(s, u)), t + s[2] * v


def extend_bounds(left, sign, right):
    return tuple(
        (lo + min(s * lower, s * upper), hi + max(s * lower, s * upper))
        for (lo, hi), s, (lower, upper) in zip(left, sign, right)
    )


def unite(a, b):
    return tuple((min(lower, x), max(upper, y)) for (lower, upper), (x, y) in zip(a, b))


@cache
def syllable(word):
    h = BB if abs(word[0]) == 3 else AA
    raw = reduce(mul, map(terms, word), ONE)
    groups = {}
    for (t, w, e), c in raw.items():
        x, y = (w, t) if h == BB else (t, w)
        xy = compose(power(TRANSLATIONS[0], x), power(TRANSLATIONS[1], y))
        signs, trans = compose(xy, h if e else IDENT)
        groups.setdefault((signs, trans[2]), []).append((trans[0], trans[1], c))
    bounds = {
        key: tuple((min(a), max(a)) for a in list(zip(*values))[:2])
        for key, values in groups.items()
    }
    return groups, bounds


@cache
def prepare(name):
    layers = [
        syllable(tuple(js)) for _, js in groupby(DATA[name], lambda j: abs(j) == 3)
    ]
    suffix = [{} for _ in range(len(layers) + 1)]
    suffix[-1][(IDENT[0], 0)] = ((0, 0), (0, 0))
    for i in reversed(range(len(layers))):
        for key, box in layers[i][1].items():
            for tail, rest in suffix[i + 1].items():
                site = multiply_key(key, tail)
                new = extend_bounds(box, key[0], rest)
                suffix[i][site] = (
                    unite(suffix[i][site], new) if site in suffix[i] else new
                )
    return layers, suffix


def coeffs(degrees):
    h = [1]
    for m, count in degrees:
        for _ in range(count):
            result = [0] * (len(h) + m - 1)
            for i, a in enumerate(h):
                for j in range(m):
                    result[i + j] += a
            h = result
    return h


def reciprocal(h, n):
    values = [1]
    for j in range(1, n + 1):
        values.append(
            -sum(h[i] * values[j - i] for i in range(1, min(j, len(h) - 1) + 1))
        )
    return values


def coefficient(name, i, j, k, r):
    if abs(i) > DATA["coordinate_bound"] or abs(j) > DATA["coordinate_bound"]:
        return 0
    sign, offset = REPS[r]
    target_z = offset[2] - 2 * k
    layers, suffix = prepare(name)
    box = suffix[0].get((sign, target_z))
    if box is None:
        return 0
    target = (2 * i + offset[0], 2 * j + offset[1])
    direction = tuple(1 if 2 * t <= lo + hi else -1 for t, (lo, hi) in zip(target, box))
    powers = [
        4 * sum(abs(letter) == axis for letter in DATA[name]) for axis in (1, 2, 3)
    ]
    shifts = (powers[0] + 2 * powers[1], powers[2])
    threshold = tuple(t - 2 * d * s for t, d, s in zip(target, direction, shifts))
    states = {IDENT: 1}
    for index, (groups, _) in enumerate(layers):
        new = Counter()
        for (s, p), value in states.items():
            for (linear, z), choices in groups.items():
                nxt, tz = multiply_key((s, p[2]), (linear, z))
                tail = tuple(a * b for a, b in zip(nxt, sign)), nxt[2] * (target_z - tz)
                rest = suffix[index + 1].get(tail)
                if rest is None:
                    continue
                limits = [
                    (cut - min(v * a, v * b) if d == 1 else cut - max(v * a, v * b))
                    for cut, d, v, (a, b) in zip(threshold, direction, nxt, rest)
                ]
                for x, y, c in choices:
                    tx, ty = p[0] + s[0] * x, p[1] + s[1] * y
                    if (
                        direction[0] * (tx - limits[0]) <= 0
                        and direction[1] * (ty - limits[1]) <= 0
                    ):
                        new[nxt, (tx, ty, tz)] += value * c
        states = {g: c for g, c in new.items() if c}
    weights = Counter()
    for (s, p), value in states.items():
        assert s == sign and p[2] == target_z
        digits = tuple(
            d * (t - v) // 2 - shift
            for d, t, v, shift in zip(direction, target, p, shifts)
        )
        assert all(a >= 0 for a in digits)
        weights[digits] += value
    if not weights:
        return 0
    hx = reciprocal(
        coeffs([(3, powers[0]), (5, powers[1])]), max(a for a, b in weights)
    )
    hy = reciprocal(coeffs([(3, powers[2])]), max(b for a, b in weights))
    return sum(c * hx[a] * hy[b] for (a, b), c in weights.items())


if __name__ == "__main__":
    arg = argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--word", choices=("u", "v"), default="u")
    arg.add_argument("--site", nargs=4, type=int, metavar=("I", "J", "K", "R"))
    opt = arg.parse_args()
    if opt.site is not None:
        if opt.site[3] not in range(4):
            arg.error("R must be 0, 1, 2 or 3 for 1, a, b or ab")
        print(coefficient(opt.word, *opt.site))
    else:
        for word, s in (("u", 1), ("v", -1)):
            for site, expected in (
                ((-1420, -208, 14, 1), 2187 * s),
                ((1419, 202, 14, 1), -2187 * s),
            ):
                c = coefficient(word, *site)
                assert c == expected
                print(word, site, c)
