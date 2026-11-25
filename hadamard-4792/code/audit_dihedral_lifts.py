"""Test every emitted sign assignment in the original 2-by-2 matrix algebra."""
import argparse
from pathlib import Path

import numpy as np


BASE = np.array([[[1, 0], [0, 1]], [[0, -1], [1, 0]], [[1, 0], [0, -1]]],
                dtype=np.int32)


def polynomial(imag, reflection, signs, n):
    positions = np.arange(n, dtype=np.int64)
    which = ((imag >> positions) & 1) + 2 * ((reflection >> positions) & 1)
    return BASE[which] * (1 - 2 * ((signs >> positions) & 1))[:, None, None]


def multiply(a, b):
    value = np.zeros((len(a) + len(b) - 1, 2, 2), dtype=np.int64)
    for j, coefficient in enumerate(a):
        value[j:j + len(b)] += coefficient @ b
    return value


def satisfies(a, b):
    # Reversal followed by transpose represents z^(n-1) times the adjoint.
    astar, bstar = a[::-1].transpose(0, 2, 1), b[::-1].transpose(0, 2, 1)
    gram = multiply(a, astar) + multiply(b, bstar)
    gram[len(a) - 1] -= 2 * len(a) * np.eye(2, dtype=np.int64)
    if np.any(gram):
        return False
    polys = (a, b, astar, bstar)
    return all(np.array_equal(multiply(polys[i], polys[j]), multiply(polys[j], polys[i]))
               for i in range(4) for j in range(i))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("assignments", type=Path, nargs="+")
    args = parser.parse_args()
    count = valid = 0
    for path in args.assignments:
        for line in path.read_text().splitlines():
            ai, av, bi, bv, signs = map(int, line.split())
            a = polynomial(ai, av, signs, args.n)
            b = polynomial(bi, bv, signs >> args.n, args.n)
            count += 1
            if satisfies(a, b):
                valid += 1
                print(f"valid pair {path} {line}")
    print(f"{count} sign assignments, {valid} satisfy the matrix identities")


if __name__ == "__main__":
    main()
