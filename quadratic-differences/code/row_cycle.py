"""Check the 52-row cycle and its scalar realization for p=5K+1 and q=5."""

import argparse
from graphlib import TopologicalSorter
from itertools import permutations
from pathlib import Path

from stripe import neighbours, square_words

HEIGHT = 52
LOW_COLUMNS = 91


def check_word(word):
    if any(word[i] == word[i + d * d]
           for d in range(1, 8) for i in range(len(word) - d * d)):
        raise ValueError("monochromatic square distance in row word")


def cycle():
    paths = []
    highs = []
    for line in Path(__file__).with_name("row-cycle.txt").read_text().splitlines():
        high, *changes = line.split()
        if len(high) != HEIGHT or set(high) - set("0123"):
            raise ValueError("invalid high word")
        check_word(high)
        highs.append(high)
        path = [high[:-1]]
        for edit in changes[0].split(",") if changes else ():
            row, colour = edit.split("=")
            row = int(row)
            if not 0 <= row < HEIGHT - 1 or colour not in "0123" or len(colour) != 1:
                raise ValueError("invalid edit")
            old = path[-1]
            if old[row] == colour:
                raise ValueError("redundant edit")
            word = old[:row] + colour + old[row + 1:]
            check_word(word)
            path.append(word)
        paths.append(path)
    if len(highs) != 5 or max(map(len, paths)) * 7 != LOW_COLUMNS:
        raise ValueError("unexpected cycle dimensions")
    for j, path in enumerate(paths):
        if path[-1] != highs[(j + 1) % len(highs)][1:]:
            raise ValueError("cycle does not close")
    return highs, paths


def verify_scalar(k):
    p, q = 5 * k + 1, 5
    if k < LOW_COLUMNS + 7:
        raise ValueError("expected K >= 98")
    highs, paths = cycle()
    n = HEIGHT * p - LOW_COLUMNS * q
    colours = bytearray([255]) * n
    for u in range(p):
        j, r = divmod(q * u, p)
        if r < p - LOW_COLUMNS * q:
            word = highs[j]
        else:
            low = (r - (p - LOW_COLUMNS * q)) // q
            path = paths[j]
            word = path[min(low // 7, len(path) - 1)]
        for row, c in enumerate(word):
            x = r + p * row
            if colours[x] != 255:
                raise ValueError("duplicate label")
            colours[x] = int(c)
    if 255 in colours:
        raise ValueError("uncoloured label")
    d = 1
    while p * d * d - q * d < n:
        for shift in (p * d * d - q * d, p * d * d + q * d):
            if any(colours[i] == colours[i + shift] for i in range(n - shift)):
                raise ValueError(f"monochromatic scalar distance {shift}")
        d += 1
    print(f"p={p}, q={q}: checked all scalar distances on {n} vertices")


def allowed_rows(word):
    adjacent = neighbours(len(word))
    allowed = [{c} for c in word]
    while True:
        remaining = [set(range(4)) - {next(iter(allowed[j])) for j in ns if len(allowed[j]) == 1}
                     for ns in adjacent]
        if remaining == allowed:
            return allowed
        allowed = remaining


def check_53():
    words = sorted(square_words(53))
    prefixes = [allowed_rows(w[:-1]) for w in words]
    suffixes = [allowed_rows(w[1:]) for w in words]
    possible = {i: set() for i in range(len(words))}
    for i, left in enumerate(words):
        for j, right in enumerate(words):
            for perm in permutations(range(4)):
                if (all(perm[c] in domain for c, domain in zip(right[1:], prefixes[i]))
                    and all(c in {perm[k] for k in domain} for c, domain in zip(left[:-1], suffixes[j]))):
                    possible[i].add(j)
                    break
    list(TopologicalSorter(possible).static_order())
    print(f"{len(words)} normalized 53-row words, {sum(map(len, possible.values()))} allowed pairs, no cycle")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("K", nargs="*", type=int, default=[98, 117, 251])
    parser.add_argument("--check-53", action="store_true", help="check the obstruction for vertical plateaus")
    args = parser.parse_args()
    if args.check_53:
        check_53()
    for k in args.K:
        verify_scalar(k)
