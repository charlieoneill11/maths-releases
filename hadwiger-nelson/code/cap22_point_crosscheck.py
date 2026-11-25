"""Independently subdivide integer boxes and eliminate square roots by squaring."""

from fractions import Fraction as F
from math import ceil, isqrt
from cap22_double_arcs import SCALE, tiered_terms, short_pair_bounds


def audit(n, constants, star):
    g = constants
    unit, short, second = (g[key] for key in ('B', 'C', 'E'))
    q = ceil(F(g['blank']) * SCALE)
    p = ceil(F(g['edge_probability']) * SCALE - F(star, 2))
    k = 2090
    denominator = 9 * n * k * (k - 1) * (k - 2) * (k - 3)
    linear = denominator - 24 * (n - 2) * (n - 3) * (denominator // ((k - 2) * (k - 3)))
    intercept = n * (n - 1) * denominator + 4 * 266 * n * (n - 1) * (n - 2) * (n - 3) * (
        denominator // (9 * k * (k - 1) * (k - 3))
    )

    def variance(m):
        return intercept + m * (linear - 2 * m * (denominator // n))

    lo, hi = 0, n * (n - 1) // 2 + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if variance(mid) < 0:
            hi = mid
        else:
            lo = mid
    max_edges = lo
    boxes = [((0, max_edges), (0, n), (0, n))]
    examined = 0
    a = 2000 - g['first_retained_per_mille']
    while boxes:
        spans = boxes.pop()
        examined += 1
        (m, M), (s, S), (j, J) = spans
        if s + j > n or n * q + M * p < SCALE:
            continue
        S, J = min(S, n - j), min(J, n - s)
        var = variance(m)
        assert var >= 0 and p >= unit

        def degree_bound(low, high):
            norm = n * high - low * low
            # First integer strictly above the Cauchy deviation, then add
            # an outward-rounded bound on the mean of this degree sum.
            deviation = 1 + isqrt(2 * var * norm // (denominator * n))
            return ceil(F(2 * M * high, n)) + deviation

        off = min(n, S + J)
        excluded = degree_bound(s + j, off)
        ext_r, ext_d = short_pair_bounds(S, J)
        r_sum = degree_bound(s, S)
        short_r = min(ext_r, r_sum, ceil(F(r_sum + 5 * S, 2)))
        short_d = min(ext_d, excluded, ceil(F(excluded + 5 * off, 2)))
        credit = tiered_terms(n, m, M, short_r, short_d, excluded, s + j, off)
        ordinary = n * q + M * p - credit
        if ordinary < SCALE:
            continue
        base = n * q + M * (p - unit) - s * short - j * second - credit
        loss = min((n - s) * g['L'], (n - s) * g['T'] + J * g['U'], J * g['J'])
        modes = (
            (1000 - g['second_retained_per_mille'], loss),
            (2000 - g['second_retained_per_mille'], 0),
        )
        for b, cost in modes:
            # Cross-multiply before squaring, using the unrounded variance.
            room = (SCALE - base - cost) * 2000 * n - 2 * M * unit * (a * S + b * J)
            norm = n * (a * a * S + b * b * J) - (a * s + b * j) ** 2
            if room > 0 and room * room * denominator > 2 * n * unit * unit * var * norm:
                break
        else:
            spans = ((m, M), (s, S), (j, J))
            axis = max(range(3), key=lambda i: (spans[i][1] - spans[i][0]) * (1, 19, 9)[i])
            a0, b0 = spans[axis]
            if a0 == b0:
                return dict(order=n, passed=False, examined=examined, witness=[m, s, j])
            cut = a0 + 2 * (b0 - a0) // 5
            for part in [(a0, cut), (cut + 1, b0)]:
                boxes.append(spans[:axis] + (part,) + spans[axis + 1 :])
    return dict(order=n, passed=True, examined=examined, edge_ceiling=max_edges)
