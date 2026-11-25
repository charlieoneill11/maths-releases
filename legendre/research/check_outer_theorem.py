"""Consolidated verification of the large-base theorem at exponent 11/5.

Every real x >= 32 654 578 787 390 has a prime in (x^{11/5}, (x+1)^{11/5}),
by three ranges:

  (I)   32 654 578 787 390 <= x <= 39e12: the twenty-mode test with the
        reduced Farey shoulder charge, the record-gap cofactor deduction and
        the convex histogram deduction, on the slabs in SLABS, plus the
        low-zero correction on the first 2.1 million bases;
  (II)  38 296 393 337 347 <= x <= 1e16: the six-mode test, condition (A);
  (III) x >= 1e16: Carneiro--Milinovich--Soundararajan, Theorem 5.

This replaces the historical chain of project notes (twelve-mode, Farey,
signed-zero refinement with Murphy's windows and the high zero packet) by a
single chain of slabs that uses none of those inputs.  Run from this
directory:  python3 -B check_outer_theorem.py   (about two minutes).

The endpoint 32 654 578 787 390 uses the zeros and the maximal-gap table
(G2) through 1.32e20.  With the option --reduced-inputs the program instead
recomputes, on the same slabs and without the zeros, the cutoff obtained
(a) with only the rows of (G2) below 2^64, (b) with the gap histogram (G1)
alone, and (c) with no prime-gap data at all (about three more minutes).
"""
from fractions import Fraction as Q
from math import isqrt

from check_bounded_factors import lowlog, highlog
from check_cutoffs import tenth_root, log_bounds
from check_three_mode import PI_LO, PI_HI
import check_continuous_farey as farey
import check_convex_cofactors as convex
import check_wheel_cofactors as wheel
from check_splice_shoulders import GRID, HEIGHT, U
from check_twenty_mode_splice import FINE, Fpair, spectral, K, modes, safe, shoulders

X0 = 32_654_578_787_390
TOP = 39_000_000_000_000
SIX = 38_296_393_337_347
CMS = 10**16
NORM = Q('.761942143419865')
MOMENT = Q('1.377680396761364')

# (left, right, k rounded down, first integer with J_k > 0 or None if J_k>0 at left)
SLABS = (
    (32_654_400_000_000, 32_654_591_400_000, Q('.900989374141681'), 32_654_580_892_712),
    (32_654_000_000_000, 32_654_728_300_000, Q('.900989355101264'), 32_654_591_385_176),
    (32_650_000_000_000, 32_657_973_000_000, Q('.900989106668924'), 32_654_728_287_294),
    (32_657_900_000_000, 32_662_000_000_000, None, None),
    (32_661_000_000_000, 32_700_000_000_000, None, None),
    (32_690_000_000_000, 32_800_000_000_000, None, None),
    (32_790_000_000_000, 33_116_944_888_557, None, None),
    (33_100_000_000_000, 33_500_000_000_000, None, None),
    (33_500_000_000_000, 35_000_000_000_000, None, None),
    (35_000_000_000_000, TOP, None, None),
)


TWELVE = 35_000_000_000_000           # Theorem outer: every real x >= 35e12
# Starting points of the continuous real range with fewer empirical inputs
# (no zeros in any of them): rows of (G2) with h_i <= 2^64 and (G1); (G1) only;
# no prime-gap data.
REDUCED = (
    ('maximal-gap table below 2^64 and histogram', True, True, 32_706_763_162_237),
    ('histogram only', False, True, 32_746_701_927_355),
    ('no prime-gap data', False, False, 32_971_281_678_698),
)

# The largest prime not exceeding 4e18, with a Pratt certificate:
# q -> (generator, factorization of q-1); factors below 2^16 by trial division.
END_PRIME = 4*10**18-113
PRATT = {
    3_999_999_999_999_999_887: (5, ((2, 1), (11, 1), (181_818_181_818_181_813, 1))),
    181_818_181_818_181_813: (5, ((2, 2), (3, 1), (29, 1), (192_631, 1), (2_712_263_549, 1))),
    2_712_263_549: (2, ((2, 2), (157, 1), (4_318_891, 1))),
    4_318_891: (2, ((2, 1), (3, 1), (5, 1), (19, 1), (7_577, 1))),
    192_631: (3, ((2, 1), (3, 1), (5, 1), (6_421, 1))),
}


def certified_prime(q):
    if q < 2**16:
        return q > 1 and all(q % d for d in range(2, isqrt(q)+1))
    g, factors = PRATT[q]
    product = 1
    for r, e in factors:
        assert certified_prime(r)
        product *= r**e
    return (product == q-1 and pow(g, q-1, q) == 1
            and all(pow(g, (q-1)//r, q) != 1 for r, _ in factors))


def histogram_end():
    """Lemma convex: (4e18-1476, 4e18] contains a prime, so with (G1) every gap
    whose smaller prime is below 4e18-1476 has length at most 1476."""
    assert 4*10**18-1476 < END_PRIME <= 4*10**18 and certified_prime(END_PRIME)


def twenty_mode_constants():
    """Lemma twenty: F(0), ||F||_1, M_F, the derivative bounds, V_0 and V_1."""
    f0, norm, moment = spectral(FINE)
    assert f0 > Q('1.000000000974554')
    assert norm < NORM and moment + Q('1e-8') <= -MOMENT
    m = modes(FINE)
    s = sum(abs(w) for _, w in m)
    assert s == Q('.761870883') and 2*K*s < 4            # sum|w| < 1, ||G||_1 < 4
    assert 2*PI_HI*K**2*s < 32                            # |F'|
    assert (2*PI_HI)**2*2*K**3/3*s < 328                  # |F''|
    lam0 = 1-Q(39, 160)**2
    k1 = sum(k*abs(w) for k, w in m)
    c1 = 4*K/PI_LO*k1/(4*K)**2*(2*PI_HI*K/lam0+Q(2, 16)/lam0**2)
    assert c1 < 2
    assert 16*32+c1/16 < 514                              # V_0
    assert 32*(16*highlog(16)-15)+c1*(highlog(16)+1)/16 < 1000   # V_1
    assert f0-164*Q('7e-9')**2 > 1                        # F >= 1 near 0
    return f0


def six_mode_constants():
    """Lemma six (derivative part), Lemma six-count and Proposition six."""
    from check_signed_kernel import MODES
    k6 = 2
    s = sum(abs(w) for _, w in MODES)
    assert s == Q('.84271') and 2*k6*s < 4
    assert (2*PI_HI)**2*k6**2*(2*k6*s) < 550              # |F_6''|
    assert sum(abs(w)*(PI_HI*k/4)**2 for k, w in MODES) < 10   # |G_6''|
    assert 2*PI_HI*k6**2*s < 22                           # |F_6'|
    lam0 = 1-Q(11, 96)**2
    k1 = sum(k*abs(w) for k, w in MODES)
    c1 = 4*k6/PI_LO*k1/(4*k6)**2*(2*PI_HI*k6/lam0+Q(2, 12)/lam0**2)
    assert c1 < 2                                         # |F_6'(y)| <= 2/y^2, y >= 12
    assert 12*22+Q(2, 12) < 613                           # V_0
    assert 22*(12*highlog(12)-11)+2*(highlog(12)+1)/12 < 1600   # V_1
    # Lemma six-count, with log a >= 60, e^30 > 10^13, e^15 > 3*10^6.
    assert highlog(10**13) < 30 and highlog(3*10**6) < 15
    assert 2*60 < Q('2e-11')*10**13 and 60 < Q('1e-11')*10**13
    assert 2*60 < Q('.001')*3*10**6
    e_lo = Q('2.718')
    assert 4/(28*e_lo) < Q('.0526')
    assert 8/(e_lo**2*(30-highlog(100))) < Q('.043')
    assert 4*Q('.01') <= Q('.04') < Q('.0526') and Q('.0526')+Q('1e-11') < Q('.053')
    # Proposition six: the remaining error terms, with log a >= 60, D < 4e-13, P < 50.
    assert 1+100*U <= Q('101.000001') and Q('101.000001')/lowlog(2) < 146
    e_pow = Q((2+146*60)*60)*U**2/10**13                  # uses e^{-30} < 10^{-13}
    assert e_pow < Q('1e-7')
    zeros = Q('8e-13')*((3+Q('.15')*highlog(2*PI_HI/Q('4e-13')))*613+Q('.15')*1600+4)
    assert zeros < Q('1e-8')
    excess = 4*(U**3-1)*50*Q('.02684511')+Q('.106')*(U**2-1)*Q('.134471')
    assert excess < Q('1e-10')
    assert e_pow+zeros+Q('1e-12')+excess < Q('2e-6')
    assert -Q('1.5366567')+Q('.106')*Q('.134471')+Q('2e-6') < -Q('1.52239')


def sieve_constants():
    """Lemmas ramare and w-constants: eta, C_0, the variation bound, the squarefree gain."""
    m = 500
    eta = sum(Q(1, k) for k in range(1, m+1))-highlog(m)-Q(1, 2*m)   # < Euler's constant
    for p in range(2, 20_001):
        if all(p % d for d in range(2, isqrt(p)+1)):
            eta += lowlog(p)/(p*(p-1))
    assert eta > farey.ETA == Q('1.33252')
    assert farey.integral_constant() > Q('1.1452')
    assert farey.derivative_error_constant() < Q('2.287')
    assert farey.squarefree_gain() > Q('.00491')


def paper_budget(strips, l, r, constant):
    """The charge of Proposition charge, with beta = [log(p_- v)]_- + c_-(z) - [log U]_+."""
    root0 = tenth_root(l)[0]
    lower = l*root0
    p = Q(11*l, 10*(l+1))*root0
    small_l = Q('1.1')*lowlog(l)
    large_l = Q('1.1')*highlog(r+1)
    charge = 0
    unit = 10**21
    for w, h in strips.items():
        v = Q(w, GRID)
        assert v < 1
        t = p*lower*v/U
        assert t > 10**10
        n = t.__floor__()-1
        z = isqrt((farey.LAMBDA*n).__floor__())
        beta = lowlog(p*v)+farey.varying_denominator(z, constant)-highlog(U)
        big = large_l if beta >= 0 else small_l
        assert big+beta > 0
        charge += (unit*8*Q(h, HEIGHT)*big*v*U**3/(big+beta)).__ceil__()
    return Q(charge, unit)


def slab_inputs(left, right):
    """The charge used by the slab equals the one described in the paper; q_0 is in the histogram."""
    layers, shape, constant = wheel.common()
    assert paper_budget(shape, left, right, constant) == wheel.budget(shape, left, right, constant)
    q0 = wheel.geometry(left, right)[3]
    assert q0 < wheel.HIST_MAX == 15*10**12


def explicit_formula_errors(l, r):
    """All x-dependent explicit-formula errors below 1e-8 on [l, r]."""
    d = Q('1.1')/l
    dmin = Q('1.1')/(r+1)
    root = l*tenth_root(l)[0]
    pmax = Q('1.1')*(r+1)*tenth_root(r+1)[1]/r
    u = Q('1.000000000001')
    assert K*d < (u-1)/u                       # e^{KD} < 1+1e-12
    assert 2*Q('1.1')*highlog(r+1)+1 < 71       # log(a e^{KD}) + 1 < 71
    assert Q(71)/lowlog(2) < 103 and 1+K*pmax*u < 67
    powers = (103*67+2)*71*u/root
    zeros = 2*d*((3+Q('.15')*highlog(7/dmin))*514+150)+10*d
    assert powers+zeros+Q('1e-9')+Q('1e-12') < Q('1e-8')


def first_root(left, right, k):
    """Least integer n >= left with J_k(n) > 0, or None if J_k(right) <= 0."""
    if wheel.comparison(left, k)[0] > 0:
        return left
    if not wheel.comparison(right, k)[0] > 0:
        return None
    lo, hi = left, right
    while hi > lo+1:
        mid = (lo+hi)//2
        if wheel.comparison(mid, k)[0] > 0:
            hi = mid
        else:
            assert wheel.comparison(mid, k)[1] < 0
            lo = mid
    return hi


def reduced_inputs():
    """Remark after Theorem sharp: the same slabs with fewer empirical inputs."""
    from check_record_cofactors import RECORDS
    layers, shape, constant = wheel.common()
    f0 = Fpair(Q(0), FINE)[0]
    for name, table, histogram, expected in REDUCED:
        roots = []
        for left, right, _, _ in SLABS:
            slab_inputs(left, right)
            gain = Q(0)
            if table:
                saved = wheel.RECORDS
                wheel.RECORDS = tuple(row for row in RECORDS if row[0] <= 2**64)
                assert len(wheel.RECORDS) == 6
                try:
                    gain += wheel.record_gain(left, right, layers)
                finally:
                    wheel.RECORDS = saved
            if histogram:
                gain += convex.convex_gain(left, right, layers)
            k = safe(f0-wheel.budget(shape, left, right, constant)+gain)
            assert k*Q('.11')*tenth_root(left)[0]*left/(left+1)-NORM > Q('1.4')   # (slope)
            roots.append((first_root(left, right, k), right))
        covered = TWELVE
        changed = True
        while changed:
            changed = False
            for root, right in roots:
                if root is not None and root < covered <= right:
                    covered, changed = root, True
        assert covered == expected, (name, covered)
        print('reduced inputs (%s, no zeros): every real x >= %d' % (name, covered), flush=True)


def range_one():
    twenty_mode_constants()
    sieve_constants()
    histogram_end()
    strips = shoulders(FINE)
    assert len(strips) == 18449 and sum(strips.values()) < Q('.14')*HEIGHT and max(strips) < GRID
    explicit_formula_errors(SLABS[0][0], TOP)
    covered_from = None
    previous_right = None
    for left, right, k, root in SLABS:
        slab_inputs(left, right)
        got_root, got_k = convex.evaluate(left, right)
        if k is not None:
            assert (got_root, got_k) == (root, k)
        else:
            assert got_root == left
        start = got_root
        if previous_right is not None:
            assert start <= previous_right, (left, start, previous_right)
        previous_right = right
        covered_from = start if covered_from is None else covered_from
    assert previous_right == TOP
    # Low zeros on [X0, first root]: same computation as the convex note.
    from check_low_zero_transport import transported
    from check_low_zero_cutoff import COUNT, HEIGHT as TOP_ZERO
    lo, hi, k, raw = SLABS[0]
    anchor = raw-2_100_000
    assert lo < X0 < anchor < raw < hi
    low = transported(anchor, X0, X0)[0]
    corrected = wheel.comparison(X0, k)[0]+Q('2.2')*low/(X0+1)
    assert low > Q('1400961.44') and corrected > Q('2.99e-14')
    assert Q('2.2')/X0*COUNT*(2+Q('2.2')*TOP_ZERO) < Q('.34')
    assert Q('1.1')*TOP_ZERO/(6*X0) < Q('7e-9')
    print('range I: every real x in [%d, %d]; low-zero margin %.3g' % (X0, TOP, float(corrected)), flush=True)


def range_two():
    import check_signed_kernel
    check_signed_kernel.check()
    six_mode_constants()
    # Condition (A) on [SIX, CMS]: log a >= 60, D < 4e-13, D sqrt(a) < 50.
    assert Q(22, 10)*lowlog(SIX) >= 60
    assert Q('1.1')/SIX < Q('4e-13')
    assert Q('1.1')*(CMS+1)*tenth_root(CMS+1)[1]/CMS < 50
    # The left side of the cutoff inequality increases faster in log x than
    # the right side on the whole range, so positivity at SIX persists.
    k = Q(110736425, 10**8)-4*Q(2684511, 10**8)
    assert k*Q('.11')*tenth_root(SIX)[0]*SIX/(SIX+1) > Q(85385123, 10**8)*(SIX+1)/SIX
    print('range II: every real x in [%d, %d]' % (SIX, CMS), flush=True)


def range_three():
    # Lemma: if Y >= 5 and Y - X - 1/2 > (22/25) sqrt(Y) log Y then (X, Y)
    # contains a prime (CMS Theorem 5).  With X = x^{11/5}, Y = (x+1)^{11/5}
    # and x >= 1e16: Y - X >= (11/5) x^{6/5}, sqrt(Y) <= (1+1e-15) x^{11/10},
    # log Y <= (11/5)(log x + 1e-16).  Dividing by (11/5) x^{11/10}, it
    # suffices that  x^{1/10} - (22/25)(1+1e-15)(log x + 1e-16) - 1e-20 > 0.
    # The left side increases in x once x^{1/10} > 8.8.
    x = CMS
    lhs = tenth_root(x)[0]
    rhs = Q(22, 25)*(1+Q('1e-15'))*(highlog(x)+Q('1e-16'))+Q('1e-20')
    assert lhs > Q('8.8') and lhs-rhs > 0
    print('range III: every real x >= %d (margin %.3f)' % (x, float(lhs-rhs)), flush=True)


if __name__ == '__main__':
    import sys
    if not __debug__:
        raise SystemExit('Run with Python assertions enabled.')
    if sys.argv[1:] == ['--reduced-inputs']:
        twenty_mode_constants()
        sieve_constants()
        histogram_end()
        explicit_formula_errors(SLABS[0][0], TOP)
        reduced_inputs()
        raise SystemExit(0)
    assert len(sys.argv) == 1, 'usage: check_outer_theorem.py [--reduced-inputs]'
    range_three()
    range_two()
    range_one()
    print('Every real x >= %d has a prime strictly between x^(11/5) and (x+1)^(11/5).' % X0)
