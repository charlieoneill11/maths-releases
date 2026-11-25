"""Build the sharp-target integer graph by its cyclic strip or direct distances."""

import argparse
from math import gcd, isqrt

from encode import clauses


def word(p, q):
    return [(i + 1) * q // p - i * q // p for i in range(p)]


def strip(p, q, numerator=57, denominator=1):
    """Encode denominator * P on [0, numerator * (p+q)]."""
    bits = word(p, q)
    heights = [numerator + sum(bits[(u - i) % p] for i in range(1, numerator + 1))
               + int(u == numerator % p) for u in range(p)]
    points = {(u, k): (u * q) % p + p * k
              for u, height in enumerate(heights) for k in range(height)}
    edges = set()
    # Prefix sums of the periodic word also handle jumps longer than p.
    for (u, k), v in points.items():
        for d in range(1, 9):
            end = u + denominator * d
            rises = end * q // p - u * q // p
            vertical = denominator * d * d
            for delta in (-vertical, vertical):
                w = points.get((end % p, k + rises + delta))
                if w is not None:
                    edges.add((min(v, w), max(v, w)))
    return set(points.values()), edges


def direct(p, q, numerator=57, denominator=1):
    span = numerator * (p + q)
    p, q = denominator * p, denominator * q
    limit = (q + isqrt(q * q + 4 * p * span)) // (2 * p)
    distances = {abs(p * d * d + q * d) for d in range(-limit, limit + 1)}
    distances = sorted(k for k in distances if 0 < k <= span)
    return span + 1, distances


def scalar_cnf(p, q, columns):
    n, distances = direct(p, q)
    # The largest component modulo gcd is sufficient, as all the other
    # residue classes are translates of it or of a prefix of it.
    step = gcd(p + q, 2 * p)
    size = (n - 1) // step + 1
    edges = [(i, i + d // step) for d in distances for i in range(size - d // step)]
    if columns:
        inv = pow(q, -1, p)

        def point(i):
            x = step * i
            u = (inv * x) % p
            v = (x - q*u) // p
            if (p+q) % 2 and (u+v) % 2:
                return u+p, v-q
            return u, v

        order = {v: i for i, v in enumerate(sorted(range(size), key=point))}
        edges = sorted((min(order[i], order[j]), max(order[i], order[j])) for i, j in edges)
    # Edge clauses forbid every common colour. In the columns variant one
    # may pick any assigned colour per vertex, respecting the two anchors.
    vertex_clauses = size if columns else 7 * size
    print("p cnf", 4 * size, vertex_clauses + 4 * len(edges) + 2)
    for c in clauses(size, edges, exactly_one=not columns):
        print(*c, 0)


def audit(bound, numerator, denominator):
    stack = [(1, 0, [0], 9, 1, [0]*8 + [1])]
    generated = set()
    while stack:
        p1, q1, w1, p2, q2, w2 = stack.pop()
        p, q = p1 + p2, q1 + q2
        if p > bound:
            continue
        w = w1 + w2
        if w != word(p, q) or (p, q) in generated:
            raise ValueError("mediant word mismatch")
        generated.add((p, q))
        stack.extend(((p1, q1, w1, p, q, w), (p, q, w, p2, q2, w2)))
    cases = 0
    for p in range(10, bound + 1):
        for q in range(1, (p - 1) // 9 + 1):
            if gcd(p, q) != 1:
                continue
            generated.remove((p, q))
            pts, edges = strip(p, q, numerator, denominator)
            n, ds = direct(p, q, numerator, denominator)
            expected = {(v, v + d) for d in ds for v in range(n - d)}
            if pts != set(range(n)) or edges != expected:
                raise ValueError(f"strip differs from scalar graph at {p}, {q}")
            cases += 1
    if generated:
        raise ValueError("unexpected slopes from the mediant traversal")
    print(f"mediant words, strip and scalar graphs agree for {cases} primitive pairs through p={bound}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_subparsers(dest="mode", required=True)
    test = mode.add_parser("audit")
    test.add_argument("bound", type=int)
    test.add_argument("--target", nargs=2, type=int, default=(57, 1), metavar=("A", "B"),
                      help="test the rational upper bound A/B")
    cnf = mode.add_parser("cnf")
    cnf.add_argument("p", type=int)
    cnf.add_argument("q", type=int)
    cnf.add_argument("--columns", action="store_true", help="use lattice order and at-least-one colour blocks")
    args = parser.parse_args()
    if args.mode == "audit":
        if args.bound < 10:
            parser.error("audit needs an upper bound of at least 10")
        a, b = args.target
        if not (b > 0 and 57 * b <= a <= 64 * b):
            parser.error("expected a target in [57, 64] with positive denominator")
        audit(args.bound, a, b)
    else:
        if not (0 < 9 * args.q < args.p and gcd(args.p, args.q) == 1):
            parser.error("expected a primitive pair with p > 9q > 0")
        scalar_cnf(args.p, args.q, args.columns)
