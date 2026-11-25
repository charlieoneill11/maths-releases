"""Generate four-colouring CNFs in DIMACS format (standard library only)."""

import argparse
from itertools import combinations
from math import isqrt


def interval(j, n):
    # For |d| > j + floor(sqrt(n)) + 1, |d| (|d| - j) > n.
    limit = j + isqrt(n) + 1
    distances = sorted({abs(d * (d + j)) for d in range(-limit, limit + 1)} - {0})
    edges = [(x, x + k) for k in distances for x in range(n - k)]
    return n, edges


def grid(width, height, parity=None, crop=False):
    points = [(u, v) for u in range(width) for v in range(height)
              if (parity is None or (u + v) % 2 == parity)
              and (not crop or ((v != 0 or u >= 8) and (v != 64 or u <= 2)))]
    index = {point: i for i, point in enumerate(points)}
    edges = []
    for i, (u, v) in enumerate(points):
        for d in range(1, isqrt(height - 1) + 1):
            for delta in (-d * d, d * d):
                other = u + d, v + delta
                if other in index:
                    edges.append((i, index[other]))
    return len(points), edges


def clauses(n, edges, *, exactly_one=True):
    blocks = [list(range(4 * v + 1, 4 * v + 5)) for v in range(n)]
    yield from blocks
    if exactly_one:
        for block in blocks:
            for a, b in combinations(block, 2):
                yield [-a, -b]
    for u, v in edges:
        for c in range(4):
            yield [-blocks[u][c], -blocks[v][c]]
    # The ends of an edge have distinct colours, so we may name them 0 and 1.
    if edges:
        u, v = edges[0]
        yield [blocks[u][0]]
        yield [blocks[v][1]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_subparsers(dest="mode", required=True)
    line = mode.add_parser("interval")
    line.add_argument("j", type=int, choices=range(9))
    line.add_argument("n", type=int)
    rect = mode.add_parser("grid")
    rect.add_argument("width", type=int)
    rect.add_argument("height", type=int)
    rect.add_argument("--parity", type=int, choices=(0, 1))
    mode.add_parser("crop", help="even component of the cropped 11 x 65 rectangle")
    args = parser.parse_args()
    if args.mode == "interval":
        if args.n < 1:
            parser.error("n must be positive")
        n, edges = interval(args.j, args.n)
    elif args.mode == "crop":
        n, edges = grid(11, 65, 0, crop=True)
    else:
        if min(args.width, args.height) < 1:
            parser.error("both dimensions must be positive")
        n, edges = grid(args.width, args.height, args.parity)
    count = 7 * n + 4 * len(edges) + (2 if edges else 0)
    print("p cnf", 4 * n, count)
    for clause in clauses(n, edges):
        print(*clause, 0)


if __name__ == "__main__":
    main()
