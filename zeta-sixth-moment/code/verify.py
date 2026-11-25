"""Check finite sixth-moment projection bounds from a TSV with integer weights.

Run python verify.py for the exact lower bounds. Add --ceiling to certify the
upper bound for the first 250 endpoint tests (NumPy and SciPy required).
--audit /path/to/pinned/lean/repo compares every grouped Gram entry with Lean.

The kernel conventions and integer normalizations are those in Fraccaro,
https://hexagonmath.org/pdf/2610.00634v3 , and the repository snapshot
https://github.com/Niklas-Fraccaro/sixth-moment-lean/tree/950bfaff8724d4adb1c37535634a139b70228df0 .
In particular see Certificate/Exact/Numerator.lean, Exact/GramEntries.lean,
and Kernels/{Balanced,Unbalanced}/IntegerEvaluator.lean under SixthMoment.
"""

import argparse
import csv
import re
from collections import namedtuple
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial, lcm
from pathlib import Path

BASE = 10**8
SCALE = 24 * BASE
D_BAL = 6 * 315 * 63063000
D_MIX = 256 * factorial(13)
NUM_DEN = 201600 * BASE**10
GRAM_DEN = 4 * SCALE**13 * lcm(D_BAL, D_MIX)
BAL_FACTOR = GRAM_DEN // (2 * SCALE**13 * D_BAL)
MIX_FACTOR = GRAM_DEN // (2 * SCALE**13 * D_MIX)
NINE_FACT = factorial(9)

Test = namedtuple("Test", "family A B polynomial")
CHEBYSHEV = [(1,), (0, 2), (-1, 0, 8), (0, -6, 0, 32), (1, 0, -32, 0, 128)]
NEWTON_COTES = (1364651, 9903168, -7587864, 35725120, -51491295, 87516288,
                -87797136, 87516288, -51491295, 35725120, -7587864, 9903168, 1364651)

# Row r describes the common numerator kernel for the monomial x^r.
# Each triple (i,j,v) represents v * a^i * b^j / 201600 for a <= b.
NUM_TERMS = [
    ((2, 1, 8400), (2, 2, -16800), (2, 3, 8400), (3, 0, -2800), (3, 2, 8400), (3, 3, -5600)),
    ((2, 2, -2100), (2, 3, 4200), (2, 4, -2100), (3, 1, 2800), (3, 2, -4200), (3, 4, 1400),
     (4, 0, -700), (4, 2, 2100), (4, 3, -1400)),
    ((2, 1, 420), (2, 2, -1260), (2, 3, 2100), (2, 4, -2100), (2, 5, 840), (3, 0, -140),
     (3, 2, -700), (3, 3, 1400), (3, 5, -560), (4, 1, 1400), (4, 2, -2100), (4, 4, 700),
     (5, 0, -280), (5, 2, 840), (5, 3, -560)),
    ((2, 2, -315), (2, 3, 1050), (2, 4, -1575), (2, 5, 1260), (2, 6, -420), (3, 1, 420),
     (3, 2, -1050), (3, 3, 1400), (3, 4, -1050), (3, 6, 280), (4, 0, -105), (4, 2, -525),
     (4, 3, 1050), (4, 5, -420), (5, 1, 840), (5, 2, -1260), (5, 4, 420), (6, 0, -140),
     (6, 2, 420), (6, 3, -280)),
    ((2, 1, 45), (2, 2, -180), (2, 3, 525), (2, 4, -1050), (2, 5, 1260), (2, 6, -840),
     (2, 7, 240), (3, 0, -15), (3, 2, -315), (3, 3, 1050), (3, 4, -1400), (3, 5, 840),
     (3, 7, -160), (4, 1, 420), (4, 2, -1050), (4, 3, 1400), (4, 4, -1050), (4, 6, 280),
     (5, 0, -84), (5, 2, -420), (5, 3, 840), (5, 5, -336), (6, 1, 560), (6, 2, -840), (6, 4, 280),
     (7, 0, -80), (7, 2, 240), (7, 3, -160)),
]


def read_certificate(path):
    tests, coefficients, original = [], [], []
    with path.open() as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            family = row["family"]
            a, b, degree = (int(row[key]) for key in ("A", "B", "degree"))
            assert int(row["row"]) == len(tests) + 1
            assert 0 < a <= b and 0 <= degree <= 4
            if family == "U":
                assert 3*a + 5*b < 2*BASE
            else:
                assert family == "V" and 4*b < BASE
            tests.append(Test(family, a, b, CHEBYSHEV[degree]))
            coefficients.append(int(row["weight"]))
            original.append(int(row["published_weight"]))
    return tests, coefficients, original


def numerator(test):
    b = test.B if test.family == "U" else BASE - test.B
    return sum(
        scalar * value * BASE**(10-i-j) * test.A**i * b**j
        for degree, scalar in enumerate(test.polynomial) if scalar
        for i, j, value in NUM_TERMS[degree]
    )


def reflect(p):
    return tuple((-1)**r * v for r, v in enumerate(p))


@lru_cache(30000)
def shifted(p, delta, sign):
    """Coefficients of SCALE^4 * p((delta + sign*x)/SCALE)."""
    return tuple(
        sum(p[r] * SCALE**(4-r) * comb(r, k) * delta**(r-k) * sign**k
            for r in range(k, len(p)))
        for k in range(len(p))
    )


def even_product(p, q):
    return [
        sum(p[i] * q[k-i] for i in range(max(0, k-len(q)+1), min(len(p)-1, k)+1))
        for k in range(0, len(p)+len(q)-1, 2)
    ]


def slice_density(t, a, b, c, d):
    """Six times the volume density of the balanced kernel at total mass t."""
    lo, hi = max(0, t-b), min(a, t)
    ll, hh = max(0, t-d), min(c, t)
    if hi <= lo or hh <= ll:
        return 0

    def primitive(x, y):
        return 3*x*x*y + max(x-y, 0)**3 - max(x+y-t, 0)**3

    return (primitive(hi, hh) - primitive(lo, hh)
            - primitive(hi, ll) + primitive(lo, ll))


@lru_cache(20000)
def balanced_moments(A, B, C, D):
    end = min(A+B, C+D)
    breaks = (A, B, C, D, A+C, A+D, B+C, B+D)
    knots = sorted({0, end} | {v for v in breaks if 0 < v < end})
    a, b, c, d = (24*v for v in (A, B, C, D))
    center = SCALE-a-b-c-d
    moments = [0]*5
    for left, right in zip(knots, knots[1:]):
        for j, weight in enumerate(NEWTON_COTES):
            t = 24*left + 2*(right-left)*j
            density = 24*(right-left)*weight*slice_density(t, a, b, c, d)
            H = (center+2*t)//2
            term = H*density
            for k in range(5):
                moments[k] += term
                term *= H*H
    return tuple(moments)


def balanced(A, B, C, D, p, q):
    delta = 12*(A+B-C-D)
    poly = even_product(shifted(p, delta, -1), shifted(q, -delta, -1))
    moments = balanced_moments(A, B, C, D)
    return sum(v * 2*(315//(2*k+1)) * moments[k] for k, v in enumerate(poly))


@lru_cache(None)
def simplex_terms(k, mask):
    """Integer multinomial coefficients after inclusion-exclusion on three caps."""
    terms = {}
    factor = factorial(k) * 2**(8-k) * factorial(13)
    for first in range(k//2+1):
        for second in range(k//2-first+1):
            third = k//2-first-second
            choices = [range(2*t+2) if mask & (1 << j) else range(1)
                       for j, t in enumerate((first, second, third))]
            for i, j, u in product(*choices):
                h = k+5-i-j-u
                key = i, j, u, h
                den = factorial(i)*factorial(j)*factorial(u)*factorial(h)
                terms[key] = terms.get(key, 0) + factor//den
    return tuple((*key, value) for key, value in terms.items())


@lru_cache(18000)
def mixed_moments(A, B, C, D):
    caps = (24*A, 24*B, 24*C)
    H = sum(caps)-24*D
    powers = [[v**i for i in range(10)] for v in caps]
    moments = [0]*5
    for mask in range(8):
        height = H - sum(v for j, v in enumerate(caps) if mask & (1 << j))
        if height <= 0:
            continue
        hp = [height**i for i in range(14)]
        sign = (-1)**mask.bit_count()
        for k in range(5):
            moments[k] += sign * sum(
                m * powers[0][i]*powers[1][j]*powers[2][u]*hp[h]
                for i, j, u, h, m in simplex_terms(2*k, mask)
            )
    return tuple(moments)


def mixed(A, B, C, D, p, q):
    if A+B+C <= D:
        return 0
    t = (SCALE-24*(A+B+C-D))//2
    poly = even_product(shifted(p, -t, 1), shifted(q, t, 1))
    return sum(v*m for v, m in zip(poly, mixed_moments(A, B, C, D)))


def gram_entry(left, right):
    family, a, b, p = left
    other, c, d, q = right
    if (family, other) == ("V", "U"):
        return gram_entry(right, left)
    if (family, other) == ("U", "U"):
        return BAL_FACTOR*(balanced(a, d, b, c, p, q)
                           + balanced(a, c, b, d, p, reflect(q)))
    if (family, other) == ("V", "V"):
        return BAL_FACTOR*balanced(a, b, c, d, p, q)
    return MIX_FACTOR*(mixed(b, c, d, a, q, p) + mixed(a, c, d, b, p, reflect(q)))


def build_gram(tests):
    gram = [[0]*len(tests) for _ in tests]
    for i, test in enumerate(tests):
        for j in range(i, len(tests)):
            gram[i][j] = gram[j][i] = gram_entry(test, tests[j])
    return gram


def quotient(vector, gram, coefficients):
    N = Fraction(sum(c*k for c, k in zip(coefficients, vector)), NUM_DEN)
    D = Fraction(sum(a * sum(b*g for b, g in zip(coefficients, row))
                     for a, row in zip(coefficients, gram)), GRAM_DEN)
    assert D > 0
    return NINE_FACT*N*N/D


def show_bracket(label, value):
    bound = value.numerator * 10**12 // value.denominator
    print(f"{label}: {bound}/10^12 <= R < {bound+1}/10^12")


def certify_ceiling(vector, gram):
    """The transform search is numerical. The positive definiteness check is exact."""
    import numpy as np
    from scipy.linalg import cholesky, solve_triangular

    g = np.array(gram, dtype=object)
    k = np.array(vector, dtype=object)
    n = len(k)
    q = Fraction(41009, 1000)
    den = q.denominator*GRAM_DEN*NUM_DEN**2
    # Q / den is exactly q times the Gram matrix minus 9! times kk^T.
    Q = q.numerator*NUM_DEN**2*g - q.denominator*NINE_FACT*GRAM_DEN*np.outer(k, k)
    qf = np.array([float(Fraction(v, den)) for v in Q.flat]).reshape(n, n)
    scales = np.sqrt(qf.diagonal())
    chol = cholesky(qf/np.outer(scales, scales), lower=True)
    approx = solve_triangular(chol.T, np.eye(n))/scales[:, None]
    W = np.array([int(round(10**8*z)) for z in approx.flat], dtype=object).reshape(n, n)
    B = W.T @ (Q @ W)
    for row, diag in zip(B, B.diagonal()):
        offdiag = sum(abs(v) for v in row)-abs(diag)
        assert diag > 0 and 10**5 * offdiag < diag
    print("Original 250-test supremum < 41009/1000 (exact positive-definiteness check)")


def audit_snapshot(snapshot, tests, old, gram):
    """Compare reconstructed entries with all 15,931 published grouped entries."""
    import numpy as np

    files = snapshot / "SixthMoment" / "Certificate"
    features = re.findall(r"⟨\.(U|V), (\d+), (\d+), (\[[^\]]+\])⟩",
                          (files / "Features.lean").read_text())
    keys = {(family, int(a), int(b)): i for i, (family, a, b, p) in enumerate(features)}
    change = np.zeros((len(keys), len(tests)), dtype=object)
    for j, test in enumerate(tests):
        change[keys[test[:3]], j] = old[j]
    actual = change @ np.array(gram, dtype=object) @ change.T
    expect = np.zeros((len(keys), len(keys)), dtype=object)
    pattern = r": pair(Zero|Minus) \((\d+),(\d+)\) = (-?\d+) :="
    count = 0
    for file in (files / "GramBlocks").glob("B*.lean"):
        for part, i, j, z in re.findall(pattern, file.read_text()):
            i, j = int(i), int(j)
            val = int(z)*(BAL_FACTOR if part == "Zero" else MIX_FACTOR)
            expect[i, j] += val//(1 if i == j else 2)
            if i != j:
                expect[j, i] += val//2
            count += 1
    assert count == 2*15931 and np.array_equal(actual, expect)
    print("All 15,931 grouped Gram entries match the pinned snapshot.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ceiling", action="store_true")
    parser.add_argument("--audit", type=Path, help="path of the pinned Lean checkout")
    parser.add_argument("--certificate", type=Path, default=Path(__file__).with_name("certificate.tsv"))
    args = parser.parse_args()
    tests, weights, old = read_certificate(args.certificate)
    assert len(tests) == 397
    vector = [numerator(test) for test in tests]
    gram = build_gram(tests)
    original = quotient(vector, gram, old)
    assert original > Fraction(41008991690, 10**9)
    show_bracket("Original weights", original)
    extended = quotient(vector, gram, weights)
    assert extended > Fraction(410298, 10000)
    show_bracket("397-test certificate", extended)

    first = [row[:250] for row in gram[:250]]
    if args.ceiling:
        certify_ceiling(vector[:250], first)
    if args.audit:
        audit_snapshot(args.audit, tests[:250], old[:250], first)


if __name__ == "__main__":
    main()
