"""Find simultaneous Z7 x F9 and Z19 x F9 solutions with a common invariant sign lift."""
from collections import defaultdict
from itertools import product
from math import prod
from random import Random
import argparse
import json

import numpy as np
from quotient import profiles, field_patterns, match


def orbit_table(generator):
    labels = np.full((7, 19), -1)
    orbits = []
    for i, j in np.ndindex(7, 19):
        if labels[i, j] >= 0:
            continue
        orbit = sorted({(i*pow(2,t,7)%7, j*pow(generator,t,19)%19) for t in range(9)})
        for x, y in orbit:
            labels[x, y] = len(orbits)
        orbits.append(orbit)
    # For the two nonsquare representatives use 3 mod 7 and 2 mod 19.
    columns = [[sum(x == k for x,y in orbit) for k in (0,1,3)]
               + [sum(y == k for x,y in orbit) for k in (0,1,2)] for orbit in orbits]
    return labels, np.array(columns, dtype=np.int16)


def sheet_fibres(generator):
    labels, columns = orbit_table(generator)
    signs = 2*((np.arange(1 << len(columns))[:, None] >> np.arange(len(columns))) & 1)-1
    margins = signs.astype(np.int16) @ columns
    fibres = defaultdict(list)
    for mask, row in enumerate(margins):
        fibres[tuple(int(n) for n in row)].append(mask)
    return labels, fibres


def choose_quotient(blocks, pattern, rng):
    groups = []
    for k in pattern:
        candidates = list(blocks[k].items())
        rng.shuffle(candidates)
        groups.append(dict(candidates))
    return match(groups)


def fibre_keys(rows7, rows19):
    return [tuple(row[k] for row in (*rows7, *rows19)) for k in range(3)]


def budgets(sizes):
    # A four-list exact match needs two pair lists. Choose the least total pair count.
    a, b, c, d = sorted(sizes)
    return a*d+b*c


def search(generator, seed, rounds):
    _, fibres = sheet_fibres(generator)
    a, _ = profiles(7)
    b, _ = profiles(19)
    patterns = sorted(set(field_patterns(a)).intersection(field_patterns(b)))
    rng = Random(seed)
    best = None
    for _ in range(rounds):
        pattern = rng.choice(patterns)
        a7 = choose_quotient(a, pattern, rng)
        a19 = choose_quotient(b, pattern, rng)
        if a7 is None or a19 is None:
            continue
        # Independently negating the 19-coordinate of a single block preserves
        # both projected identities. It can change the number of compatible lifts.
        min_sizes, best_rows = [], []
        for r, s in zip(a7, a19):
            options = []
            for variant in (s, (s[0], s[2], s[1])):
                keys = fibre_keys(r, variant)
                size = prod(len(fibres.get(k, ())) for k in keys)
                if size:
                    options.append((size, variant))
            if not options:
                break
            size, rows = min(options)
            min_sizes.append(size)
            best_rows.append(rows)
        if len(min_sizes) != 4:
            continue
        bound = budgets(min_sizes)
        if best is None or bound < best[0]:
            best = bound, dict(generator=generator, field=pattern, rows7=a7, rows19=best_rows,
                               block_lifts=min_sizes, sheet_masks=[
                                   [fibres[k][0] for k in fibre_keys(r, s)] for r, s in zip(a7, best_rows)])
    return best


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=4792)
    parser.add_argument("--rounds", type=int, default=1000)
    parser.add_argument("--generator", type=int, choices=(4, 5), default=4)
    args = parser.parse_args()
    result = search(args.generator, args.seed, args.rounds)
    if result is None:
        raise SystemExit("no common lift found in the sampled projected solutions")
    print(json.dumps(result[1], indent=2))
