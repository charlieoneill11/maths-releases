"""Refute bounded periods for one binary coordinate of a four-colouring."""

import argparse
from math import gcd, isqrt
from pathlib import Path
import subprocess
import tempfile

from encode import grid


def orientations(m):
    # Multiplying by a unit relabels the binary word. Reflecting u replaces
    # a by b-a in coordinates (u,(v-u)/2), up to a constant phase.
    seen = set()
    units = [k for k in range(m) if gcd(k, m) == 1]
    for a in range(m):
        for b in range(m):
            if (a, b) in seen or gcd(gcd(a, b), m) != 1:
                continue
            seen.update((v * u % m, b * u % m) for u in units for v in (a, b-a))
            yield a, b


def maximal_divisors(m):
    for prime in range(2, m + 1):
        if m % prime == 0 and all(prime % k for k in range(2, isqrt(prime) + 1)):
            yield m // prime


def instance(m, a, b, width, height):
    pts = [(u, v) for u in range(width) for v in range(height) if (u + v) % 2 == 0]
    n, edges = grid(width, height, 0)
    primary = [1 + (a * u + b * ((v-u)//2)) % m for u, v in pts]
    clauses = [[1]]  # Complement both values of the primary bit if necessary.
    for i, j in edges:
        x, y = primary[i], primary[j]
        s, t = m + i + 1, m + j + 1
        if x == y:
            clauses.extend(([s, t], [-s, -t]))
        else:
            for h in (1, -1):
                for k in (1, -1):
                    clauses.append([h*x, h*y, k*s, k*t])
    last = m + n
    for shift in maximal_divisors(m):
        different = []
        for i in range(m - shift):
            last += 1
            different.append(last)
            x, y = i+1, i+shift+1
            clauses.extend(([-last, x, y], [-last, -x, -y]))
        clauses.append(different)
    # The two loop lengths in the arithmetic argument differ in their
    # 2-adic valuations. Each residue class modulo 16 must see both bits.
    if m % 16 == 0 and a % 2 and (b-6*a) % 16 == 0:
        for r in range(16):
            xs = list(range(r+1, m+1, 16))
            clauses.extend((xs, [-x for x in xs]))
    return last, clauses


def verify_case(m, a, b, width, height, checker, tmp):
    from pysat.solvers import Glucose4
    nv, cs = instance(m, a, b, width, height)
    with Glucose4(bootstrap_with=cs, with_proof=True) as solver:
        if solver.solve():
            return False
        proof = solver.get_proof()
    cnf, cert = tmp / "palette.cnf", tmp / "palette.drat"
    with cnf.open("w") as out:
        print("p cnf", nv, len(cs), file=out)
        for c in cs:
            print(*c, 0, file=out)
    cert.write_text("\n".join(proof) + "\n")
    p = subprocess.run([checker, str(cnf), str(cert)], capture_output=True, check=True)
    if b"s VERIFIED" not in p.stdout.splitlines():
        raise RuntimeError(f"checker did not verify {(m,a,b)}")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checker", help="compiled drat-trim executable")
    parser.add_argument("--first", type=int, default=1)
    parser.add_argument("--last", type=int, default=64)
    args = parser.parse_args()
    if not 1 <= args.first <= args.last:
        parser.error("expected a positive range")
    vertical = short = large = 0
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        for m in range(args.first, args.last + 1):
            for a, b in orientations(m):
                if (2*a-b) % m == 0:
                    vertical += 1
                elif verify_case(m, a, b, 15, 55, args.checker, tmp):
                    short += 1
                elif verify_case(m, a, b, 43, 58, args.checker, tmp):
                    large += 1
                else:
                    raise RuntimeError(f"palette not excluded at {(m,a,b)}")
            print(f"through {m}: vertical={vertical} small={short} large={large}", flush=True)


if __name__ == "__main__":
    main()
