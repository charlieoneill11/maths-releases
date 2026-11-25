"""Exact rational verification of nine sextic and septic correction profiles.

Run beside chowla_one_exception_certificate.py, or set PYTHONPATH to that directory.
The coefficient search is external to this standard-library verification.
"""
from fractions import Fraction

import chowla_one_exception_certificate as quintic


# (Wick degree, 160 times the common cutoff width, Legendre degree, weight times 10^7).
PROFILES = (
    (6, 20, 2, -53945511),
    (6, 20, 4,  45352129),
    (7, 16, 2, -11243176),
    (6, 18, 2,   9261068),
    (6, 20, 6,  -7416954),
    (6, 16, 4,  36415509),
    (6, 24, 2,  -8230813),
    (6, 24, 4,    939245),
    (7, 20, 2,  11527588),
)
INHERITED_WEIGHT = Fraction(1014885461, 10**16)
CERTIFIED_PROPORTION = Fraction("0.94532732177059")


def certify():
    cubic = quintic.cubic
    quartic = quintic.quart
    subgrid = cubic.subgrid
    center = cubic.moments.integer_spline(cubic.splines.approximate_H())
    inherited_rows = [
        ((width,) if width else (), profile, size)
        for width, profile, size in subgrid.linear
    ]
    inherited_rows.extend(((a, b), profile, size) for a, b, profile, size in subgrid.pairs)
    old_lower, old_upper = cubic.moments.central_bounds(
        center, subgrid.linear, subgrid.pairs
    )
    quartic_profiles = [((a,) * 4, c) for a, c in quartic.QUARTIC_ROWS]
    for widths, coefficients in [*cubic.CUBIC_ROWS, *quartic_profiles, *quintic.QUINTIC_ROWS]:
        row = quartic.profile_row(widths, coefficients)
        inherited_rows.append(row)
        lower, upper = quartic.central_enclosure(center, row)
        old_lower += lower
        old_upper += upper

    baseline = (19 - cubic.COT_UPPER) / 16
    inherited_gain = quintic.CERTIFIED_PROPORTION - baseline
    assert old_upper >= old_lower > 0 and inherited_gain > 0
    old_norm_upper = old_upper**2 / (2 * inherited_gain)
    z = INHERITED_WEIGHT
    gain = z * old_lower
    cost = z**2 * old_norm_upper
    prior = []
    for degree, width, legendre, numerator in PROFILES:
        row = quartic.profile_row((width,) * degree, [0] * (legendre // 2 - 1) + [1])
        w = Fraction(numerator, 10**7)
        lower, upper = quartic.central_enclosure(center, row)
        gain += w * (lower if w > 0 else upper)
        cost += 2 * w * z * sum(quintic.inner(row, old) for old in inherited_rows)
        cost += 2 * w * sum(v * quintic.inner(row, other) for v, other in prior)
        cost += w**2 * quintic.inner(row, row)
        prior.append((w, row))
    return baseline + gain - cost / 2


if __name__ == "__main__":
    bound = certify()
    assert CERTIFIED_PROPORTION < bound < CERTIFIED_PROPORTION + Fraction(1, 10**14)
    print("Verified central nonvanishing proportion above 0.94532732177059.")
