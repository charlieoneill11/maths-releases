"""Independent affine-map and cyclotomic product checker, also for JSON pairs.

JSON format: {"u":[[i,j,k,r,c], ...], "v":[...]} with nonzero integer c.
Without --modulus, acceptance requires a nontrivial two-sided integral unit.
"""

import argparse
from collections import Counter
import json
from pathlib import Path

IDENT = ((1, 1, 1), (0, 0, 0))
AA = ((1, -1, -1), (1, 1, 0))
BB = ((-1, 1, -1), (0, 1, 1))


def compose(g, h):
    a, t = g
    b, s = h
    return tuple(x * y for x, y in zip(a, b)), tuple(
        v + x * w for v, x, w in zip(t, a, s)
    )


def power(g, n):
    if n < 0:
        a, t = g
        return power((a, tuple(-s * x for s, x in zip(a, t))), -n)
    r = IDENT
    while n:
        if n % 2:
            r = compose(r, g)
        g = compose(g, g)
        n //= 2
    return r


REPS = IDENT, AA, BB, compose(AA, BB)
TRANSLATIONS = [power(g, 2) for g in REPS[1:]]


def evaluate(g):
    i, j, k, r = g
    p = IDENT
    for a, n in zip(TRANSLATIONS, (i, j, k)):
        p = compose(p, power(a, n))
    return compose(p, REPS[r])


def exact_products(u, v, modulus=None):
    def convert(p):
        return {evaluate(g): c for g, c in p.items()}

    def multiply(x, y):
        d = Counter()
        for g, c in x.items():
            for h, b in y.items():
                d[compose(g, h)] += c * b
        if modulus:
            d = {g: c % modulus for g, c in d.items()}
        return {g: c for g, c in d.items() if c}

    u, v = convert(u), convert(v)
    return multiply(u, v), multiply(v, u)


def phase_product(u, v):
    out = Counter()
    for g, e in u.items():
        for h, f in v.items():
            degree = (e + f) % 8
            out[compose(g, h), degree % 4] += 1 if degree < 4 else -1
    return {k: c for k, c in out.items() if c}


def check_file(path, modulus):
    with open(path) as f:
        data = json.load(f)
    polys = []
    for name in ("u", "v"):
        poly = {}
        for row in data[name]:
            if len(row) != 5 or any(type(x) is not int for x in row):
                raise ValueError("expected five integers")
            *g, c = row
            if (
                g[3] not in range(4)
                or tuple(g) in poly
                or not c
                or (modulus and not c % modulus)
            ):
                raise ValueError("invalid or repeated support entry")
            poly[tuple(g)] = c
        polys.append(poly)
    u, v = polys
    uv, vu = exact_products(u, v, modulus)
    if uv != {IDENT: 1} or vu != {IDENT: 1} or len(u) < 2:
        raise ValueError("pair fails two-sided nontrivial unit test")
    print(
        "two-sided products verified",
        "mod " + str(modulus) if modulus else "over Z",
        len(u),
        len(v),
    )


def published():
    from examples import cyclotomic_pair, field_pair
    from ring import ball, mul

    assert compose(compose(power(BB, -1), power(AA, 2)), BB) == power(AA, -2)
    assert compose(compose(power(AA, -1), power(BB, 2)), AA) == power(BB, -2)
    sites = ball(4)
    assert len({evaluate(g) for g in sites}) == 83
    assert all(
        compose(evaluate(g), evaluate(h)) == evaluate(mul(g, h))
        for g in sites
        for h in sites
    )
    # Independent BFS on affine isometries, then sort by the documented
    # normal form to decode the frozen census text.
    reached = frontier = {IDENT}
    for _ in range(4):
        frontier = {
            compose(g, h)
            for g in frontier
            for h in (AA, BB, power(AA, -1), power(BB, -1))
        } - reached
        reached = reached | frontier

    def normal_key(site):
        sign, t = site
        r = next(i for i, (s, _) in enumerate(REPS) if s == sign)
        delta = [a - b for a, b in zip(t, REPS[r][1])]
        assert all(v % 2 == 0 for v in delta)
        return delta[0] // 2, delta[1] // 2, -delta[2] // 2, r

    ordered = sorted(reached, key=normal_key)
    rows = Path(__file__).with_name("census52.txt").read_text().splitlines()
    profiles = Counter()
    for row in rows:
        support = [ordered[int(i)] for i in row.split()]
        profiles[
            tuple(
                sum(n % 2 for n in Counter((s[j], t[j]) for s, t in support).values())
                for j in range(3)
            )
        ] += 1
    assert profiles == {(5, 5, 1): 52}
    print("affine axes (x,y,z):", dict(profiles))
    for p in (2, 3):
        u, v = field_pair(p)
        assert exact_products(u, v, p) == ({IDENT: 1}, {IDENT: 1})
        print("field", p, "supports", len(u), len(v), "both products 1")
    u, v = ({evaluate(g): c for g, c in p.items()} for p in cyclotomic_pair())
    assert phase_product(u, v) == phase_product(v, u) == {(IDENT, 0): 1}
    print("Z[zeta_8] supports", len(u), len(v), "both products 1")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pair", nargs="?", type=Path)
    parser.add_argument("--modulus", type=int)
    args = parser.parse_args()
    if args.modulus is not None and args.modulus < 2:
        parser.error("modulus must be at least 2")
    if args.pair:
        check_file(args.pair, args.modulus)
    else:
        published()
