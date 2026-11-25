"""Check the integer cutoffs at exponent 11/5 using rational enclosures."""

from fractions import Fraction as Q
from functools import cache


SCALE = 2**200


def tenth_root(n):
    """Bracket n**(1/10) between adjacent multiples of 1/SCALE."""
    target = n * SCALE**10
    lo = 0
    hi = 1 << ((target.bit_length() + 9) // 10)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**10 <= target:
            lo = mid
        else:
            hi = mid
    return Q(lo, SCALE), Q(hi, SCALE)


def log_reduced(x):
    """For 1 <= x <= 2, sum 2*atanh((x-1)/(x+1)) and bound its tail."""
    assert 1 <= x <= 2
    z = Q(x - 1, x + 1)
    z2 = z * z
    power = z
    partial = 0
    for k in range(72):
        partial += power / (2 * k + 1)
        power *= z2
    tail = power / (145 * (1 - z2))
    return 2 * partial, 2 * (partial + tail)


LOG2_LO, LOG2_HI = log_reduced(2)


@cache
def log_bounds(x):
    """Enclose log(x), using powers of two to reduce its argument."""
    x = Q(x)
    assert x >= 1
    k = x.numerator.bit_length() - x.denominator.bit_length()
    if x < 2**k:
        k -= 1
    lo, hi = log_reduced(x / 2**k)
    lo += k * LOG2_LO
    hi += k * LOG2_HI
    return Q((lo * SCALE).__floor__(), SCALE), Q((hi * SCALE).__ceil__(), SCALE)


def check_sign(label, n, lo, hi, sign):
    assert lo <= hi
    assert (lo > 0 if sign > 0 else hi < 0), (label, n, lo, hi)
    print(label, n, '+' if sign > 0 else '-')


def integral_primitive(y):
    """Bound an antiderivative of (1 - 4.62 y^2) log(1/y) near zero."""
    assert 0 < y <= Q(45, 100)
    log_lo, log_hi = log_bounds(1 / y)
    const = y - Q(462, 900) * y**3
    coeff = y - Q(462, 300) * y**3
    return const + coeff * log_lo, const + coeff * log_hi


def check_cutoffs():
    small = 3_883_853_444_450
    limit = 70_500_000_000_000
    assert small**11 < limit**10 < (small + 1)**11
    print('Proposition 3.4 last integer', small)

    log10_lo, log10_hi = log_bounds(10)
    lower = (10 * (log10_lo + log_bounds(log10_lo)[0]))**10
    upper = (10 * (log10_hi + log_bounds(log10_hi)[1]))**10
    threshold = 921_755_345_005_754
    assert threshold - 1 < lower <= upper < threshold
    print('Lemma 3.3 first integer', threshold)

    threshold = 571_412_224_574_295
    for n in (threshold - 1, threshold):
        root_lo, root_hi = tenth_root(n)
        log_lo, log_hi = log_bounds(n)
        check_sign('(5)', n, root_lo - Q(22, 25) * log_hi,
                   root_hi - Q(22, 25) * log_lo, 1 if n == threshold else -1)

    # n^(11/5) = n^2 * (n^(1/10))^2, n^(11/10) = n * n^(1/10).
    for n in range(571_412_224_574_285, threshold):
        root_lo, root_hi = tenth_root(n)
        next_lo, next_hi = tenth_root(n + 1)
        log_lo, log_hi = log_bounds(n)
        c = Q(22, 25) * Q(11, 5) * n
        lo = ((n + 1)*next_lo)**2 - 1 - (n*root_hi)**2 - c*root_hi*log_hi
        hi = ((n + 1)*next_hi)**2 - 1 - (n*root_lo)**2 - c*root_lo*log_lo
        check_sign('(6)', n, lo, hi, 1 if n >= 571_412_224_574_286 else -1)

    threshold = 230_763_157_912_198
    for n in (threshold - 1, threshold):
        root_lo, root_hi = tenth_root(n)
        log_lo, log_hi = log_bounds(Q(10 * (n + 1), 11))
        c = Q(5 * n, 4 * (n + 1))
        lo = c * root_lo - log_hi - Q(116, 100)
        hi = c * root_hi - log_lo - Q(116, 100)
        check_sign('CMS (6.16) sufficient condition', n, lo, hi,
                   1 if n == threshold else -1)

    small_lo, small_hi = integral_primitive(Q(1, 10**7))
    large_lo, large_hi = integral_primitive(Q(45, 100))
    assert Q(130, 100) < 2*(large_lo - small_hi) <= 2*(large_hi - small_lo)
    print('Lower bound for twice the log-weighted integral exceeds 1.30')

    threshold = 111_802_817_320_536
    for n in (threshold - 1, threshold):
        root_lo, root_hi = tenth_root(n)
        log_lo, log_hi = log_bounds(Q(10 * (n + 1), 11))
        c = Q(627 * n, 500 * (n + 1))
        lo = c * root_lo - log_hi + Q(2, 5)
        hi = c * root_hi - log_lo + Q(2, 5)
        check_sign('Refined sufficient condition', n, lo, hi,
                   1 if n == threshold else -1)

    threshold = 68_599_491_157_461
    for n in (threshold - 1, threshold, 70_000_000_000_000):
        root_lo, root_hi = tenth_root(n)
        log_lo, log_hi = log_bounds(Q(10 * (n + 1), 11))
        c = Q(627 * n, 500 * (n + 1))
        lo = c * root_lo - log_hi + Q(143, 100)
        hi = c * root_hi - log_lo + Q(143, 100)
        check_sign('Refined sufficient condition with 1.43', n, lo, hi,
                   1 if n >= threshold else -1)


if __name__ == '__main__':
    check_cutoffs()
    # Global real-base exponent 2.213365. Here T^s = N.
    s = Q(2_213_365, 2_000_000)
    N = 70_500_000_000_000
    lower, upper = 3_260_204_713_976, 3_260_204_713_977
    log_N_lo, log_N_hi = log_bounds(N)
    assert s * log_bounds(lower)[1] < log_N_lo
    assert log_N_hi < s * log_bounds(upper)[0]
    u_lo, u_hi = (lower + 1) / s, (upper + 1) / s
    g_lo = Q(114, 100)*N/u_hi - log_bounds(u_hi)[1] + Q(143, 100)
    g_hi = Q(114, 100)*N/u_lo - log_bounds(u_lo)[0] + Q(143, 100)
    assert Q(300349887, 10**12) < g_lo <= g_hi < Q(300349897, 10**12)

    assert 2 * log_N_lo > 60
    assert log_bounds(lower)[0] > 1 / (s - 1)
    assert log_bounds(upper)[1] < 30 and Q(N, upper) > 21
    log_max_lo, log_max_hi = log_bounds(10**15)
    assert log_bounds(39)[1] < (s - 1) * log_max_lo
    assert (s - 1) * log_max_hi < log_bounds(40)[0]
    assert log_max_hi < 35
    print('Real-base exponent 2.213365: 0.000300349887 < g(T) < 0.000300349897')
