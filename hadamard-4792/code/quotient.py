"""Fourier conditions on Z_p x F_9 for the order-36 Spence multiplier family."""
from collections import defaultdict
from itertools import combinations_with_replacement, permutations, product
from math import isqrt
import argparse
import json


def signed_sums(weights):
    values = {0}
    for w in weights:
        values = {x + s*w for x in values for s in (-1, 1)}
    return sorted(values)


def transform(row):
    a, b, c = row
    return a + 4*b + 4*c, a + b - 2*c, a - 2*b + c


def profiles(p, retain_all=False):
    zero_weights, nonzero_weights = (([1, 3, 3], [1]*7) if p == 19
                                     else ([1, 9, 9], [1] + [3]*6))
    zero = signed_sums(zero_weights)
    nonzero = signed_sums(nonzero_weights)
    # Key the first Z_p-orbit row by its F_9 transforms at the trivial character.
    zero_rows = defaultdict(list)
    for row in product(zero, repeat=3):
        z = transform(row)
        zero_rows[z[0]].append((z, row))
    m = (p-1)//2
    other_rows = [(transform(row), row) for row in product(nonzero, repeat=3)]
    blocks = defaultdict(dict)
    candidates = 0
    for i, (a, ra) in enumerate(other_rows):
        # Inverting Z_p interchanges squares and nonsquares (p = 3 mod 4).
        for b, rb in other_rows[i:]:
            for z, rz in zero_rows.get(1-m*(a[0]+b[0]), ()):
                u, v = (z[k]+m*(a[k]+b[k]) for k in (1, 2))
                if max(abs(u), abs(v)) > isqrt(4792):
                    continue
                norms = tuple(((2*zj-aj-bj)**2 + p*(aj-bj)**2)//4
                              for zj, aj, bj in zip(z, a, b))
                if max(norms) <= 4792:
                    candidates += 1
                    if retain_all:
                        blocks[u, v].setdefault(norms, []).append((rz, ra, rb))
                    else:
                        blocks[u, v].setdefault(norms, (rz, ra, rb))
    return blocks, candidates


def field_patterns(keys):
    # Normalize block DC to +1. Permuting all four blocks preserves the equations.
    values = sorted({u for u, v in keys} | {v for u, v in keys})
    squares = [xs for xs in combinations_with_replacement(values, 4)
               if sum(x*x for x in xs) == 4792]
    patterns = set()
    for us, vs in product(squares, repeat=2):
        for perm in set(permutations(vs)):
            entries = tuple(sorted(zip(us, perm)))
            if all(e in keys for e in entries):
                patterns.add(entries)
    return sorted(patterns)


def match(groups):
    # The two pair lists need not have comparable sizes.
    g0, g1, g2, g3 = groups
    sums = {}
    for a in g0:
        for b in g1:
            x, y, z = (a[k]+b[k] for k in range(3))
            if max(x, y, z) <= 4792:
                sums[(x, y, z)] = (a, b)
    for c in g2:
        for d in g3:
            need = tuple(4792-c[k]-d[k] for k in range(3))
            if need in sums:
                a, b = sums[need]
                return [g[n] for g, n in zip(groups, (a, b, c, d))]
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("p", type=int, choices=(7, 19))
    args = parser.parse_args()
    blocks, candidates = profiles(args.p)
    patterns = field_patterns(blocks)
    print(f"{candidates} normalized blocks up to inversion, {sum(map(len, blocks.values()))} signatures, "
          f"{len(blocks)} field profiles, {len(patterns)} four-block field patterns", flush=True)
    for pattern in sorted(patterns, key=lambda pat: max(len(blocks[k]) for k in pat)):
        witness = match([blocks[k] for k in pattern])
        if witness:
            print(json.dumps({"p": args.p, "field": pattern, "orbit_rows": witness}))
            break
