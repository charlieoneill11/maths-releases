"""Numerical check of the bridge lemma (Lemma "Bridge", Section 3 of the paper).

For point tests of the two classical families, compare
  * the Schur-side quantities <v,h> and <h,h'>, computed by direct cubature of
    the projected Pieri features over the chamber 0<x<y<z<1, with
  * Fraccaro's numerator and Gram kernels, as implemented with exact integers
    in verify.py (which reproduces Fraccaro's published certificate).

Agreement to cubature accuracy is evidence that the kernels used in the paper
are the Schur inner products, including the overall normalisation (no factor of 2,
6 or 9! is lost). This is a floating-point diagnostic, not a certificate:
the cubature uses the midpoint rule on cubes of side 2/grid and 1/grid
with Richardson extrapolation, on twelve rows of certificate.tsv (rows 0 and
249 and ten drawn by numpy.random.default_rng(1)). It reports the largest
relative numerator error and the largest Gram discrepancy divided by the largest Gram entry,
and asserts both are below 5e-3 (observed at grid 240: 1.5e-3 and 5.5e-4).
Run: python bridge_check.py [grid]   (default grid 240).
"""

import sys
from fractions import Fraction

import numpy as np

import verify as V

BASE = V.BASE


def poly_eval(coeffs, t):
    out = np.zeros_like(t)
    for c in reversed(coeffs):
        out = out * t + c
    return out


def feature(x, y, z, alpha, beta, coeffs):
    """Raw Pieri feature H_{alpha,beta,p} at points of the chamber."""
    s = alpha + beta
    j = x + y + z - s
    lo = np.maximum.reduce([y, s - y, np.full_like(y, alpha), np.full_like(y, beta)])
    hi = np.minimum(z, s - x)
    length = np.clip(hi - lo, 0, None)
    return np.where((j >= 0) & (j <= 1), poly_eval(coeffs, 0.5 - j) * length, 0.0)


def projected(x, y, z, test):
    family, A, B, coeffs = test
    a, b = A / BASE, B / BASE
    beta = 1 - b if family == "U" else b
    raw = feature(x, y, z, a, beta, coeffs)
    reflected = feature(1 - z, 1 - y, 1 - x, a, beta, coeffs)
    return (raw + reflected) / 2


def chamber_grid(n):
    """Midpoints of the cubes of side 1/n whose centres satisfy x<y<z."""
    c = (np.arange(n) + 0.5) / n
    for i in range(n):
        x = c[i]
        Y, Z = np.meshgrid(c[i + 1:], c[i + 1:], indexing="ij")
        mask = Y < Z
        yield np.full(mask.sum(), x), Y[mask], Z[mask]


def schur_side(tests, n):
    k = len(tests)
    num = np.zeros(k)
    gram = np.zeros((k, k))
    cell = 1.0 / n**3
    for x, y, z in chamber_grid(n):
        v = 0.5 * (z - y) * (z - x) * (y - x)
        feats = np.array([projected(x, y, z, t) for t in tests])
        num += feats @ v * cell
        gram += feats @ feats.T * cell
    return num, gram


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    tests, _, _ = V.read_certificate(V.Path(V.__file__).with_name("certificate.tsv"))
    rng = np.random.default_rng(1)
    picks = sorted(set(rng.choice(len(tests), 10, replace=False).tolist()) | {0, 249})
    sample = [tests[i] for i in picks]
    exact_num = [Fraction(V.numerator(t), V.NUM_DEN) for t in sample]
    exact_gram = [[Fraction(V.gram_entry(s, t), V.GRAM_DEN) for t in sample] for s in sample]

    coarse = schur_side(sample, n // 2)
    fine = schur_side(sample, n)
    # Richardson extrapolation assuming first-order cubature error.
    num = 2 * fine[0] - coarse[0]
    gram = 2 * fine[1] - coarse[1]

    print(f"grid {n}; tests {picks}")
    worst = 0.0
    for i, t in enumerate(sample):
        e = float(exact_num[i])
        rel = abs(num[i] - e) / abs(e)
        worst = max(worst, rel)
        print(f"numerator {t.family} A={t.A} B={t.B} deg={len(t.polynomial)-1}: "
              f"kernel {e:.6e} schur {num[i]:.6e} rel {rel:.1e}")
    scale = max(abs(float(g)) for row in exact_gram for g in row)
    gworst = max(abs(gram[i][j] - float(exact_gram[i][j])) / scale
                 for i in range(len(sample)) for j in range(len(sample)))
    print(f"largest Gram discrepancy relative to the largest entry: {gworst:.1e}")
    print(f"largest relative numerator discrepancy: {worst:.1e}")
    assert worst < 5e-3 and gworst < 5e-3, "bridge mismatch"
    print("Bridge check passed: Fraccaro's kernels are the Schur inner products.")


if __name__ == "__main__":
    main()
