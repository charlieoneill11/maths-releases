"""Check all saved interval and grid certificates. Only drat-trim needs compiling."""

import argparse
import gzip
import json
import subprocess
import sys
import tempfile
from itertools import combinations
from math import isqrt
from pathlib import Path

import encode

ROOT = Path(__file__).resolve().parent


def require(test, message):
    if not test:
        raise ValueError(message)


def is_distance(j, k):
    # d^2 + jd = +/-k iff a discriminant j^2 +/- 4k has a
    # nonnegative integral square root of the same parity as j.
    for disc in (j * j - 4 * k, j * j + 4 * k):
        if disc >= 0:
            root = isqrt(disc)
            if root * root == disc and (root - j) % 2 == 0:
                return True
    return False


def check_interval(row, checker, scratch):
    j, w, word = row["j"], row["W"], row["colouring"]
    require(len(word) == w - 1 and set(word) <= set("0123"), f"bad witness j={j}")
    _, edges = encode.interval(j, w)
    expected = {(a, b) for a, b in combinations(range(w), 2) if is_distance(j, b - a)}
    require(len(edges) == len(expected) and set(edges) == expected, "encoder mismatch")
    require(all(word[a] != word[b] for a, b in expected if b < len(word)),
            f"monochromatic edge j={j}")
    cnf, proof = scratch / "case.cnf", scratch / "case.drat"
    with cnf.open("wb") as out:
        subprocess.run([sys.executable, str(ROOT / "encode.py"), "interval", str(j), str(w)],
                       stdout=out, check=True)
    proof.write_bytes(gzip.decompress((ROOT / "certificates" / f"j{j}.drat.gz").read_bytes()))
    result = subprocess.run([checker, str(cnf), str(proof)], check=True, capture_output=True)
    require(b"s VERIFIED" in result.stdout.splitlines(), f"unverified proof j={j}")
    print(f"j={j} W={w} edges={len(edges)} colouring and DRAT verified")


def check_odd_packing(j, w):
    # On the larger parity class, translate the first point of an
    # independent set to zero. Enumerate its remaining points in order.
    m = (w + 1) // 2
    distances = {k for k in range(1, m) if is_distance(j, 2 * k)}
    target = (m + 3) // 4

    def can_extend(candidates, need):
        if need == 0:
            return True
        for i, x in enumerate(candidates):
            if len(candidates) - i < need:
                break
            tail = [y for y in candidates[i + 1:] if y - x not in distances]
            if can_extend(tail, need - 1):
                return True
        return False

    initial = [x for x in range(1, m) if x not in distances]
    require(not can_extend(initial, target - 1), "independence bound failed")
    print(f"j={j}: no independent {target}-set in the parity class of size {m}")


def check_grid():
    rows = (ROOT / "grid-tile.txt").read_text().splitlines()
    require(len(rows) == 8 and all(len(row) == 16 and set(row) <= set("0123") for row in rows),
            "bad grid tile")
    def colour(u, v):
        return rows[u % 8][v % 16]

    for u in range(8):
        for v in range(16):
            for d in range(1, 8):
                require(all(colour(u, v) != colour(u + d, v + sign * d * d)
                            for sign in (-1, 1)), "bad torus edge")

    # Count and test unordered edges by their coordinate differences.
    for width, height in [(58, 58), (11, 65)]:
        points = [(u, v) for u in range(width) for v in range(height)]
        ids = range(len(points))
        expected = set()
        for i, k in combinations(ids, 2):
            u, v = points[i]
            x, y = points[k]
            if x > u and abs(y - v) == (x - u) ** 2:
                expected.add((i, k))
                if height == 58:
                    require(colour(u, v) != colour(x, y), "bad square edge")
        n, edges = encode.grid(width, height)
        require(n == len(points) and len(edges) == len(expected) and set(edges) == expected,
                "grid encoder mismatch")
        print(f"{width} x {height}: {n} vertices and {len(edges)} edges checked")
        if height == 65:
            even = [i for i in ids if sum(points[i]) % 2 == 0]
            idx = {i: k for k, i in enumerate(even)}
            sub = {(idx[a], idx[b]) for a, b in expected if a in idx and b in idx}
            vertices, edges = encode.grid(width, height, 0)
            require((n, len(expected), vertices, len(sub)) == (715, 4864, 358, 2436)
                    and len(edges) == len(sub) and set(edges) == sub, "bad rectangle component")
            kept = [i for i in even if (points[i][1] != 0 or points[i][0] >= 8)
                    and (points[i][1] != 64 or points[i][0] <= 2)]
            idx = {i: k for k, i in enumerate(kept)}
            sub = {(idx[a], idx[b]) for a, b in expected if a in idx and b in idx}
            vertices, edges = encode.grid(11, 65, 0, crop=True)
            require(vertices == len(kept) == 350 and len(sub) == len(edges) == 2362
                    and set(edges) == sub, "bad cropped component")
            print(f"cropped component: {vertices} vertices and {len(edges)} edges checked")
    print("8 x 16 torus verified for both signs and all d=1,...,7")


def check_flexible_tile():
    rows = (ROOT / "flexible-tile.txt").read_text().splitlines()
    require(len(rows) == 8 and all(len(row) == 16 and set(row) <= set("0123") for row in rows),
            "bad flexible tile")

    def colour(u, v):
        return rows[u % 8][(v % 32) // 2]

    for u in range(8):
        for v in range(u % 2, 32, 2):
            for d in range(1, 8):
                for sign in (-1, 1):
                    require(colour(u, v) != colour(u+d, v+sign*d*d), "bad flexible-tile edge")
    neighbours = {colour(d, s*d*d) for d in range(-7, 8) if d for s in (-1, 1)}
    require(colour(0, 0) == "0" and neighbours == {"2"}, "star is not monochromatic")
    print("8 x 32 parity tile verified: all neighbours of the origin have colour 2")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("drat_trim", help="path to compiled drat-trim")
    args = parser.parse_args()
    rows = json.loads((ROOT / "thresholds.json").read_text())
    require([r["j"] for r in rows] == list(range(9)), "missing or reordered case")
    with tempfile.TemporaryDirectory() as temp:
        for row in rows:
            check_interval(row, args.drat_trim, Path(temp))
            if row["j"] in (1, 3, 7):
                check_odd_packing(row["j"], row["W"])
    check_grid()
    check_flexible_tile()


if __name__ == "__main__":
    main()
