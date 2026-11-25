"""Search cyclic four-colourings for the steps d=1,...,7, in both signs."""

import argparse
from math import gcd


def four_colour(adj):
    n = len(adj)
    masks = [15] * n
    unused = set(range(n))

    def visit(used):
        if not unused:
            return True
        v = min(unused, key=lambda i: (masks[i].bit_count(), -len(adj[i]), i))
        unused.remove(v)
        # Permute the as-yet unnamed colours, and try just the first new one.
        for c in range(min(used + 1, 4)):
            bit = 1 << c
            if not masks[v] & bit:
                continue
            changed = [w for w in adj[v] if w in unused and masks[w] & bit]
            for w in changed:
                masks[w] ^= bit
            if all(masks[w] for w in changed) and visit(max(used, c + 1)):
                return True
            for w in changed:
                masks[w] |= bit
        unused.add(v)
        return False

    return visit(0)


def search(bound):
    loops = searches = 0
    for m in range(1, bound + 1):
        units = [u for u in range(m) if gcd(u, m) == 1]
        seen = set()
        for a in range(m):
            for b in range(m):
                if (a, b) in seen or gcd(gcd(a, b), m) != 1:
                    continue
                seen.update((u*a % m, sign*u*b % m) for u in units for sign in (-1, 1))
                steps = {(a*d*d + b*d) % m for d in range(-7, 8) if d}
                if 0 in steps:
                    loops += 1
                    continue
                searches += 1
                sym = steps | {(-s) % m for s in steps}
                adj = [{(x + s) % m for s in sym} for x in range(m)]
                if four_colour(adj):
                    return m, a, b
    print(f"through modulus {bound}: {loops} loops, {searches} exhaustive four-colour searches")
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bound", type=int)
    args = parser.parse_args()
    if args.bound < 1:
        parser.error("bound must be positive")
    hit = search(args.bound)
    if hit:
        print("colourable modulus and coefficients", *hit)
