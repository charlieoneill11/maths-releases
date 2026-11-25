"""Exact rational improvement of the inherited central nonvanishing witness.

Run beside chowla_sextic_septic_certificate.py, or put its directory on
PYTHONPATH. Tuples list the cutoff widths on the inherited 1/160 grid,
the even Legendre degree and the integer numerator of the coefficient.
"""
from fractions import Fraction

import chowla_sextic_septic_certificate as prior

DENOMINATOR = 10**8
PROFILES = (
    ((8, 16, 32, 64), 2, 30312549),
    ((8, 16, 32, 64), 4, -5245954),
    ((8, 20, 32, 68), 2, -62542918),
    ((12, 16, 24, 64), 2, -66526833),
    ((12, 16, 24, 64), 4, 59046867),
    ((12, 20, 32, 60), 2, -27804655),
    ((12, 20, 32, 60), 4, 63571537),
    ((14,) * 8, 4, -5630338346),
    ((14,) * 8, 6, 7851010526),
    ((16,) * 8, 2, 5266380051),
    ((16,) * 8, 4, -4222736926),
    ((16, 24, 40, 48), 2, 49847039),
    ((18,) * 8, 2, 1657319238),
)
CERTIFIED_PROPORTION = Fraction("0.9453286989")


def certify(additional_profiles=()):
    """Certify this witness with additional (widths, Legendre coefficients, weight) rows."""
    contraction = prior.quintic
    cubic = contraction.cubic
    quartic = contraction.quart
    center = cubic.moments.integer_spline(cubic.splines.approximate_H())
    inherited = [
        ((width,) if width else (), profile, size)
        for width, profile, size in cubic.subgrid.linear
    ]
    inherited.extend(((a, b), profile, size)
                     for a, b, profile, size in cubic.subgrid.pairs)
    quartic_rows = [((width,) * 4, coefficients)
                    for width, coefficients in quartic.QUARTIC_ROWS]
    for widths, coefficients in [*cubic.CUBIC_ROWS, *quartic_rows,
                                  *contraction.QUINTIC_ROWS]:
        inherited.append(quartic.profile_row(widths, coefficients))
    fitted_rows = []
    for degree, width, order, numerator in prior.PROFILES:
        row = quartic.profile_row((width,) * degree,
                                  [0] * (order // 2 - 1) + [1])
        fitted_rows.append((Fraction(numerator, 10**7), row))

    bound = prior.CERTIFIED_PROPORTION
    profiles = [(widths, [0] * (order // 2 - 1) + [1], Fraction(numerator, DENOMINATOR))
                for widths, order, numerator in PROFILES]
    for widths, coefficients, weight in [*profiles, *additional_profiles]:
        row = quartic.profile_row(widths, coefficients)
        if not widths:
            # The deterministic optimum is orthogonal to each direction h(0)=0.
            lower = upper = 0
        elif len(widths) == 1:
            (width,), profile, size = row
            lower, upper = cubic.moments.central_bounds(
                center, [(width, profile, size)], [])
        else:
            lower, upper = quartic.central_enclosure(center, row)
        bound += weight * (lower if weight > 0 else upper)
        inherited_inner = sum(contraction.inner(row, item) for item in inherited)
        bound -= weight * prior.INHERITED_WEIGHT * inherited_inner
        bound -= weight * sum(coefficient * contraction.inner(row, item)
                              for coefficient, item in fitted_rows)
        bound -= weight**2 * contraction.inner(row, row) / 2
        fitted_rows.append((weight, row))
    return bound


if __name__ == "__main__":
    result = certify()
    assert result > CERTIFIED_PROPORTION
    print(f"Verified central nonvanishing proportion above {float(CERTIFIED_PROPORTION):.13f}.")
