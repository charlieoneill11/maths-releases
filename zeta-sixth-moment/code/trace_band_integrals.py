"""Independent polynomial integration for the near-critical geometric coefficients."""
from sympy import Rational, expand, factorial, integrate, symbols

r, k = symbols('r k')
q = Rational
a = 2*r - 3*k
k_max = (18-7*r)/21
split = (4*r-1)/6


def integral(t, lower_k, upper_k, lower_r, upper_r):
    """Integrate out x, then k, then r on one polynomial cell."""
    after_x = factorial(9)/128 * (a**4*t**3/3 - 2*a**2*t**5/5 + t**7/7)
    primitive = integrate(expand(after_x), k)
    after_k = expand(primitive.subs(k, upper_k) - primitive.subs(k, lower_k))
    return integrate(after_k, (r, lower_r, upper_r))


if __name__ == "__main__":
    half = q(1, 2)
    switch = q(43, 42)
    endpoint = q(15, 14)
    narrow = (integral(1-a, half, split, 1, switch)
              + integral(a, split, k_max, 1, switch)
              + integral(1-a, half, k_max, switch, endpoint))
    balanced = integral(k-half, r/2, k_max, 1, q(36, 35))
    coefficient = 42 - 2*(q(209, 1024)-narrow)
    ideal_ceiling = 42 - q(55, 1024) + 2*balanced
    assert coefficient == q(2578241177999, 61983140352)
    assert 2*balanced == q(134173355669, 1470888975150000000)
    assert ideal_ceiling == q(493586674117277079727, 11767111801200000000)
    print('narrow mass per orientation', narrow, 'balanced mass per orientation', balanced)
    print('near-critical coefficient', coefficient,
          'ceiling with R, before F+ (F+ increment: mixed_row_checks.py, section 4)', ideal_ceiling)

    # Legacy check: a thin factorable window (1/2<k<0.5000001, 8k/25<x<9k/25)
    # from an earlier draft. It is NOT the factorable region of the paper;
    # the factorable stage 41.6117... is computed in
    # factorable_polygon_check.py and factorable_row_checks.py, and the
    # release coefficient 41.6406... in mixed_row_checks.py.
    # In this window the narrow-gap upper endpoint is z=1/2+x and the
    # near-critical boundary sets the lower endpoint.
    x, z = symbols('x z')
    density = factorial(9)/4 * (k-2*x)**2 * (z-x)**2 * (z-k+x)**2
    primitive_z = integrate(expand(density), z)
    integral_z = expand(primitive_z.subs(z, half+x) - primitive_z.subs(z, (18-28*k)/7))
    primitive_x = integrate(integral_z, x)
    integral_x = expand(primitive_x.subs(x, 9*k/25) - primitive_x.subs(x, 8*k/25))
    factorable_extra = 2*integrate(integral_x, (k, half, q(5000001, 10000000)))
    from trace_band_geometry import factorable_extra_mass, ordered_band
    narrow_half = ordered_band[:-1] + [(0, -2, -2, 3), (2, 0, -2, 1), (0, 2, 0, -1)]
    assert factorable_extra == factorable_extra_mass(narrow_half)
    print('legacy thin factorable window (not the paper region) extra mass', factorable_extra)
