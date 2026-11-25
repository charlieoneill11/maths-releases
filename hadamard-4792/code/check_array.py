"""Rebuild the order-4792 Hadamard matrix from its twelve orbit masks and check it.

The matrix is built with the block formulas of the paper's bordered array
(the Goethals-Seidel array M and the border S), not from the certificate.
The script then checks H H^T = 4792 I, reads the published CSV file, checks
its Gram matrix, and compares the two matrices entry by entry.

Usage: python3 check_array.py H4792.csv.gz      (needs Python 3.10+ and NumPy)

Products are computed in double precision. Every partial sum is an integer
of absolute value at most 4792, so the arithmetic is exact.
"""
import gzip
import hashlib
import itertools
import sys

import numpy as np

MODULI = (7, 19, 3, 3)
ORDER = 4792
MASKS = {  # masks for the origin, the nonzero squares and the nonsquares of F_9
    "a": (0x0C85B, 0x1C32A, 0x03CDC),
    "b": (0x08573, 0x07C3C, 0x187C2),
    "c": (0x08328, 0x09E3D, 0x16D4B),
    "d": (0x04AD2, 0x03E65, 0x1991B),
}


def orbit_index():
    """Index of the orbit of (x, y) under (x, y) -> (2x, 4y), orbits sorted by least element."""
    def orbit(p):
        points = []
        while p not in points:
            points.append(p)
            p = (2 * p[0] % 7, 4 * p[1] % 19)
        return points
    least = sorted({min(orbit((x, y))) for x in range(7) for y in range(19)})
    if len(least) != 17:
        raise SystemExit("expected 17 orbits on Z7 x Z19")
    return {(x, y): least.index(min(orbit((x, y)))) for x in range(7) for y in range(19)}


def main(csv_path):
    points = list(itertools.product(*(range(k) for k in MODULI)))
    m = len(points)
    index = orbit_index()
    signs = {}
    for name, masks in MASKS.items():
        signs[name] = np.array(
            [-1 if (masks[(u != 0) + (v != 0)] >> index[x, y]) & 1 else 1 for x, y, u, v in points],
            dtype=np.int64)
    sums = {name: int(s.sum()) for name, s in signs.items()}
    print("negative-set sizes", {n: int((s < 0).sum()) for n, s in signs.items()}, "sign sums", sums)

    P = np.array(points)
    mod = np.array(MODULI)
    # Developed matrices X[g, h] = x(h - g) and the reflection R[g, h] = [h = -g].
    diff = np.ravel_multi_index(((P[None, :, :] - P[:, None, :]) % mod).transpose(2, 0, 1).reshape(4, -1),
                                MODULI).reshape(m, m)
    A, B, C, D = (signs[n][diff].astype(np.float64) for n in "abcd")
    R = np.zeros((m, m))
    R[np.arange(m), np.ravel_multi_index(((-P) % mod).T, MODULI)] = 1

    paf = A @ A.T + B @ B.T + C @ C.T + D @ D.T
    off = paf[~np.eye(m, dtype=bool)]
    print("summed autocorrelation: diagonal", set(np.diag(paf).tolist()), "off-diagonal", set(off.tolist()))

    M = np.block([[A, B @ R, C @ R, D @ R],
                  [-B @ R, A, D.T @ R, -C.T @ R],
                  [-C @ R, -D.T @ R, A, B.T @ R],
                  [-D @ R, C.T @ R, -B.T @ R, A]])
    a, b, c, d = (sums[n] for n in "abcd")
    S = np.array([[a, b, c, d], [-b, a, d, -c], [-c, -d, a, b], [-d, c, -b, a]], dtype=np.float64)
    ones = np.ones((m, 1))
    H = np.block([[-S, np.kron(S, ones.T)], [np.kron(S, ones), M]])
    ok = H.shape == (ORDER, ORDER) and set(np.unique(H).tolist()) == {-1.0, 1.0}
    rebuilt = np.array_equal(H @ H.T, ORDER * np.eye(ORDER))
    print(f"rebuilt matrix: order {H.shape[0]}, entries +-1: {ok}, H H^T = {ORDER} I: {rebuilt}")

    raw = gzip.open(csv_path).read() if csv_path.endswith(".gz") else open(csv_path, "rb").read()
    print(f"CSV: {len(raw)} bytes, sha256 {hashlib.sha256(raw).hexdigest()}")
    lines = raw.split(b"\n")
    if lines[-1] != b"":
        raise SystemExit("CSV must end with a line feed")
    table = {b"1": 1.0, b"-1": -1.0}
    F = np.array([[table[e] for e in line.split(b",")] for line in lines[:-1]])
    from_file = F.shape == (ORDER, ORDER) and np.array_equal(F @ F.T, ORDER * np.eye(ORDER))
    same = np.array_equal(F, H)
    print(f"CSV matrix: shape {F.shape}, F F^T = {ORDER} I: {from_file}, equal to rebuilt matrix: {same}")
    if not (ok and rebuilt and from_file and same):
        raise SystemExit("check failed")
    print("all checks passed")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    main(sys.argv[1])
