"""Generate the sharp-target rectangle test with the forced affine patterns."""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, permutations

from encode import clauses


def phase(x, y):
    return 2 * (x % 2) + ((y - x) // 2) % 2


@lru_cache(maxsize=2)
def minimal_seeds(parity):
    points = [(x, y) for x in range(9) for y in range(10) if (x + y) % 2 == parity]
    index = {p: i for i, p in enumerate(points)}
    requirements = []
    for x, y in points:
        masks = [0] * 4
        for d in (1, 2, 3):
            for dx in (-d, d):
                for dy in (-d*d, d*d):
                    pt = x + dx, y + dy
                    if pt in index:
                        masks[phase(*pt)] |= 1 << index[pt]
        requirements.append([m for c, m in enumerate(masks) if c != phase(x, y)])
    # The first fifteen points are the three columns x=0,1,2.
    target = (1 << 15) - 1

    def forces(active):
        while active & target != target:
            before = active
            for i, (a, b, c) in enumerate(requirements):
                if active & a and active & b and active & c:
                    active |= 1 << i
            if before == active:
                return False
        return True

    minimal = []
    for size in range(16):
        for bits in combinations(range(15), size):
            mask = sum(1 << i for i in bits)
            if not any(other & mask == other for other in minimal) and forces(mask):
                minimal.append(mask)
    return [[(*points[i], phase(*points[i])) for i in range(15) if mask >> i & 1]
            for mask in minimal]


def patterns():
    found = set()
    for parity in (0, 1):
        for cells in minimal_seeds(parity):
            for reflect_x in (False, True):
                for reflect_y in (False, True):
                    points = sorted((2 * (2-x if reflect_x else x),
                                     4 * (9-y if reflect_y else y), c)
                                    for x, y, c in cells)
                    names = {}
                    found.add(tuple((x, y, names.setdefault(c, len(names))) for x, y, c in points))
    return sorted(found)


def cnf(width, height, wrap):
    pts = [(u, v) for u in range(width) for v in range(height) if (u + v) % 2 == 0]
    idx = {p: i for i, p in enumerate(pts)}

    def horizontal(u):
        return u % width if wrap else u

    edges = [(i, idx[other]) for i, (u, v) in enumerate(pts) for d in range(1, 8)
             for s in (-1, 1) if (other := (horizontal(u+d), v+s*d*d)) in idx]
    result = list(clauses(len(pts), edges))
    models = patterns()
    for u in range(width if wrap else width-4):
        for v in range(2, height-38):
            if (u + v) % 2:
                continue
            for cells in models:
                labels = [(4*idx[horizontal(u+x), v+y], c) for x, y, c in cells]
                for perm in permutations(range(4)):
                    result.append([-(i+perm[c]+1) for i, c in labels])
    return 4 * len(pts), result


def torus_audit():
    pts = [(u, v) for v in range(16) for u in range(v % 2, 8, 2)]
    idx = {p: i for i, p in enumerate(pts)}
    adj = [0] * len(pts)
    groups = defaultdict(list)
    for i, (u, v) in enumerate(pts):
        x, y = u // 2, v // 4
        groups[v % 4, (x+y) % 2].append((i, phase(x, y)))
        for d in range(1, 8):
            for s in (-1, 1):
                j = idx[(u+d) % 8, (v+s*d*d) % 16]
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    count = Counter()
    words = [-1] * len(pts)
    classes = [0] * 4

    def visit(left, used):
        if not left:
            good = 0
            for group in groups.values():
                seen = {r: words[i] for i, r in group}
                good += len(set(seen.values())) == 4 and all(seen[r] == words[i] for i, r in group)
            count[good] += 1
            return
        best, choices, score = 0, [], 200
        remaining = left
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            i = bit.bit_length() - 1
            domain = [c for c in range(min(4, used + 1)) if not adj[i] & classes[c]]
            if not domain:
                return
            value = 32 * len(domain) - (adj[i] & left).bit_count()
            if value < score:
                best, choices, score = i, domain, value
        bit = 1 << best
        for c in choices:
            words[best] = c
            classes[c] |= bit
            visit(left ^ bit, max(used, c + 1))
            classes[c] ^= bit

    visit((1 << len(pts)) - 1, 0)
    if count != {6: 4608, 7: 3552, 8: 1968}:
        raise ValueError(f"unexpected torus distribution {count}")
    return count


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    sub.add_parser("audit")
    encode = sub.add_parser("cnf")
    encode.add_argument("width", type=int)
    encode.add_argument("height", type=int)
    encode.add_argument("--wrap", action="store_true")
    args = parser.parse_args()
    if args.mode == "audit":
        counts = Counter(map(len, patterns()))
        if counts != {8: 8, 10: 8}:
            raise ValueError(f"unexpected pattern sizes {counts}")
        print("8 patterns of size eight and 8 of size ten verified")
        print("affine components per normalized torus colouring", sorted(torus_audit().items()))
    else:
        if not 5 <= args.width <= 58 or not 41 <= args.height <= 58:
            parser.error("expected width 5..58 and height 41..58")
        if args.wrap and (args.width < 8 or args.width % 2):
            parser.error("wrap needs even width >= 8")
        n, cs = cnf(args.width, args.height, args.wrap)
        print("p cnf", n, len(cs))
        for c in cs:
            print(*c, 0)
