"""Single exceptional cumulant formula for marked normal-ordered rows."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import cache
import chowla_quartic_single_certificate as quart

cubic = quart.cubic

@cache
def cross_matchings(left, right):
    """Unmatched widths and the sum of Gaussian cross-matching weights."""
    if not left:
        return {right: 1}
    a, tail = left[0], left[1:]
    result = defaultdict(Q)
    for rest, weight in cross_matchings(tail, right).items():
        result[tuple(sorted((a,) + rest))] += weight
    for b, count in Counter(right).items():
        index = right.index(b)
        other = right[:index] + right[index+1:]
        factor = 2 * count * min(a,b)**2
        for rest, weight in cross_matchings(tail, other).items():
            result[rest] += factor * weight
    return dict(result)

@cache
def tail_cumulant(widths):
    if sum(widths) <= 1:
        return 0
    if len(widths) == 2:
        return -(sum(widths)-1)**2
    return cubic.base.rect(widths)

@cache
def contraction(left, right):
    assert sum(left) <= 1 and sum(right) <= 1
    out = defaultdict(Q)
    for rest, weight in cross_matchings(left, right).items():
        out[rest] += weight
        if sum(rest) <= 1:
            continue
        out[()] += weight * tail_cumulant(rest)
        for a, count in Counter(rest).items():
            i = rest.index(a)
            out[(a,)] += weight * count * tail_cumulant(rest[:i] + rest[i+1:])
    return {k:v for k,v in out.items() if v}

def inner(left, right):
    a, first, _ = left
    b, second, _ = right
    profile = cubic.moments.convolution(first, second)
    return sum(weight * cubic.marked_cumulant(profile, rest)
               for rest, weight in contraction(a,b).items())


def certify():
    center = cubic.moments.integer_spline(cubic.splines.approximate_H())
    old = [((t,) if t else (), profile, weight)
           for t, profile, weight in cubic.subgrid.linear]
    old.extend(((a,b), profile, weight) for a,b,profile,weight in cubic.subgrid.pairs)
    lower, upper = cubic.moments.central_bounds(
        center, cubic.subgrid.linear, cubic.subgrid.pairs)
    for dims, coeffs in [*cubic.CUBIC_ROWS,
                          *[((a,)*4, co) for a,co in quart.QUARTIC_ROWS]]:
        row = quart.profile_row(dims, coeffs)
        old.append(row)
        lo, hi = quart.central_enclosure(center, row)
        lower += lo
        upper += hi
    p0 = (19-cubic.COT_UPPER)/16
    norm = upper**2 / (2*(quart.CERTIFIED_PROPORTION-p0))
    for dims, coeffs in QUINTIC_ROWS:
        row = quart.profile_row(dims, coeffs)
        lo, _ = quart.central_enclosure(center, row)
        lower += lo
        norm += 2 * sum(inner(row, previous) for previous in old) + inner(row,row)
        old.append(row)
    assert lower > 0 and norm > 0
    return p0+lower**2/(2*norm)

QUINTIC_ROWS = [
    ((16,)*5, [1779892, -8867799]),
    ((20,)*5, [4580, -5962351]),
    ((24,)*5, [-4232853, 814887]),
    ((28,)*5, [-1185699, -85106]),
    ((8,12,16,24,64), [22938237]),
    ((12,16,20,32,48), [-11687453]),
]
CERTIFIED_PROPORTION = Q("0.945325784098260")

if __name__ == "__main__":
    result = certify()
    assert CERTIFIED_PROPORTION < result < CERTIFIED_PROPORTION + Q(1,10**15)
    print("Verified central nonvanishing lower proportion above 0.945325784098260.")
