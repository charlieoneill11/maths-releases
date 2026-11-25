"""Independently validate every clause of the decisive 12-by-58 DIMACS input."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path


@lru_cache(maxsize=None)
def forces_column_block(seed):
    """Propagate literal colours on the available auxiliary vertices."""
    parity = (seed[0][0] + seed[0][1]) % 2
    points = {(x, y) for x in range(-6, 9) for y in range(10) if (x+y) % 2 == parity}
    fixed = {(x, y): c for x, y, c in seed}
    if len(fixed) != len(seed) or not fixed.keys() <= points:
        return False
    neighbours = {v: [w for w in points if 1 <= abs(w[0]-v[0]) <= 3
                      and abs(w[1]-v[1]) == (w[0]-v[0])**2] for v in points}
    while True:
        before = len(fixed)
        for v, ns in neighbours.items():
            seen = {fixed[w] for w in ns if w in fixed}
            if v in fixed:
                if fixed[v] in seen:
                    return True
            elif len(seen) == 4:
                return True
            elif len(seen) == 3:
                fixed[v] = (set(range(4)) - seen).pop()
        if len(fixed) == before:
            break
    block = [(x, y) for x, y in points if 0 <= x < 3]
    if any(v not in fixed for v in block):
        return False
    # Test equality of colours against membership of the difference in 2L.
    for (x, y), (a, b) in combinations(block, 2):
        same_phase = (x-a) % 2 == 0 and (y-b-x+a) % 4 == 0
        if (fixed[x, y] == fixed[a, b]) != same_phase:
            return False
    return True


def valid_exclusion(assignment):
    left = min(u for u, v, c in assignment)
    right = max(u for u, v, c in assignment)
    bottom = min(v for u, v, c in assignment)
    top = max(v for u, v, c in assignment)
    for u0 in range(max(0, right-4), min(left, 7)+1):
        for v0 in range(max(2, top-36), min(bottom, 19)+1):
            if (u0+v0) % 2 or any((u-u0) % 2 or (v-v0) % 4 for u, v, c in assignment):
                continue
            names = {}
            seed = tuple(((u-u0)//2, (v-v0)//4, names.setdefault(c, len(names)))
                         for u, v, c in sorted(assignment))
            if forces_column_block(seed):
                return True
    return False


def audit(path):
    points = [(u, v) for u in range(12) for v in range(58) if (u+v) % 2 == 0]
    expected = set()
    for i in range(len(points)):
        block = tuple(4*i+c+1 for c in range(4))
        expected.add(block)
        expected.update(tuple(sorted((-a, -b))) for a, b in combinations(block, 2))
    edges = set()
    for i, j in combinations(range(len(points)), 2):
        u, v = points[i]
        x, y = points[j]
        if 1 <= abs(x-u) <= 7 and abs(y-v) == (x-u)**2:
            edges.add((i, j))
            expected.update(tuple(sorted((-(4*i+c+1), -(4*j+c+1)))) for c in range(4))
    anchors = []
    exclusions = Counter()
    with path.open() as f:
        header = f.readline().split()
        if header[:3] != ["p", "cnf", str(4*len(points))]:
            raise ValueError("incorrect DIMACS header")
        count = 0
        for line in f:
            count += 1
            literals = list(map(int, line.split()))
            if literals.pop() != 0 or any(abs(v) not in range(1, 4*len(points)+1) for v in literals):
                raise ValueError("invalid DIMACS clause")
            if len(literals) == 1 and literals[0] > 0:
                anchors.append(divmod(literals[0]-1, 4))
            elif len(literals) in (8, 10) and all(v < 0 for v in literals):
                data = [divmod(-v-1, 4) for v in literals]
                if not valid_exclusion([(*points[i], c) for i, c in data]):
                    raise ValueError(f"unjustified pattern in clause {count}")
                exclusions[len(literals)] += 1
            else:
                expected.remove(tuple(sorted(literals)))
    if count != int(header[3]) or expected or len(anchors) != 2:
        raise ValueError("wrong clause count, incomplete grid or invalid symmetry breaking")
    (i, c), (j, k) = sorted(anchors)
    if c == k or (i, j) not in edges:
        raise ValueError("anchors must name distinct colours at adjacent vertices")
    print(f"{len(points)} vertices, {len(edges)} edges, {count} clauses")
    print("individually justified pattern clauses by size", sorted(exclusions.items()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cnf", type=Path)
    audit(parser.parse_args().cnf)
