"""Certified height-slice quadrature for the full six-label wave."""

import json
from fractions import Fraction as F
from pathlib import Path

from flint import arb, ctx, fmpq


def check(profile, subdivisions=256):
    S = 10**12
    H = S // 2
    x = profile['x']
    rows = profile['right']
    assert profile['left'] == [[0, 0], [H // 2, 0], [H, 0]]
    right = dict(rows)
    step = H // (len(rows) - 1)
    assert rows == [[i * step, right[i * step]] for i in range(len(rows))] and rows[-1][0] == H
    assert (
        F(9, 10) * S < x < S
        and 4 * S // 5 < min(right.values()) <= max(right.values()) < F(99, 100) * S
    )
    assert all(right[H - y] == r and right[(y + H // 2) % H] == 2 * x - r for y, r in rows)
    assert all(abs(b - a) <= step for (_, a), (_, b) in zip(rows, rows[1:]))
    # Adjacent-column angular support lies below sin(theta)=3/4, since
    # positive horizontal width requires cos(theta)>2x-r > 4/5.
    assert 2 * x - max(right.values()) > 4 * S // 5
    ctx.prec = 100
    den = 2 * subdivisions * S
    inv = arb(fmpq(1, den))
    offset = arb(fmpq(2 * x, S))
    ratio = arb(fmpq(3, 4))
    total = arb(0)
    for (h, r), (_, R) in zip(rows, rows[1:]):
        for k in range(1, 2 * subdivisions, 2):
            yy = inv * (h * 2 * subdivisions + k * step)
            rr = inv * (r * 2 * subdivisions + k * (R - r))
            adj = offset - rr
            v = ratio - yy
            # At the midpoint, exact signs are unnecessary at a switching
            # height: the antiderivative expression is nonnegative also on
            # the opposite side of the switch, so including it is safe.
            if not rr * rr + yy * yy < 1:
                ua = yy.asin() - rr.acos()
                total += rr * ua - yy + (1 - rr * rr).sqrt()
            if not adj * adj + v * v > 1:
                cv = adj.acos() - v.asin()
                total += (1 - adj * adj).sqrt() - v - adj * cv
    bins = (len(rows) - 1) * subdivisions
    # f' is Lipschitz with constant 64 on each affine-profile interval.
    # Composite midpoint error after averaging f is at most 64*d^2/24.
    error = F(64, 24) * F(1, 2 * bins) ** 2
    prob = (
        2
        * (total / bins + arb(fmpq(error.numerator, error.denominator)))
        / (arb.pi() * arb(fmpq(x, S)))
    )
    scaled = (prob.upper() * 10**18).ceil().unique_fmpz()
    assert scaled is not None
    upper = F(int(scaled), 10**18)
    edges = (upper.denominator - 1) // upper.numerator
    return dict(
        profile_intervals=len(rows) - 1,
        midpoints=bins,
        mean_slice_error=str(error),
        edge_probability_upper=str(upper),
        ppm=float(upper * 10**6),
        edges=edges,
    )


if __name__ == '__main__':
    profile = json.loads(Path(__file__).with_name('cap22_finite_edge_profile.json').read_text())
    print(json.dumps(check(profile), indent=2))
