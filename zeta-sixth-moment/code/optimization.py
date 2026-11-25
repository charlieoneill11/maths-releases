"""Verify exact rational bounds for the Fraccaro test-function optimization.

Run with Python 3 and SymPy: python optimization.py

We use z >= t >= s for the three parts of a rescaled partition and put
w = t+s. The target Schur coefficient is (z-t)(z-s)(t-s)/2. All reported
bounds include the normalization 9!. Each integral uses polynomial
antiderivatives over rational affine intervals.
"""

from functools import cache
from math import factorial

import sympy as sp


z, t, s, r, u, w = sp.symbols("z t s r u w")
q = sp.Rational
quarter = q(1, 4)
half = q(1, 2)
normalization = factorial(9)


def integrate(expression, variable, lower, upper):
    antiderivative = sp.Poly(expression, variable).integrate()
    return sp.expand(antiderivative.eval(upper) - antiderivative.eval(lower))


def shape_masses():
    # Fold the chamber under reflection so s <= r = 1-z. The other half
    # has equal mass. Here u=t-s and span=1-s-r.
    span = 1 - s - r
    squared_vandermonde = u**2 * (span - u)**2 * span**2

    def chamber_slice(s_lo, s_hi, r_lo, r_hi, u_lo):
        inner = integrate(squared_vandermonde, u, u_lo, span)
        return integrate(integrate(inner, r, r_lo, r_hi), s, s_lo, s_hi)

    # Factor 2 for reflection times 1/4 for the squared target.
    scale = q(normalization, 2)
    total = scale * chamber_slice(0, half, s, 1-s, 0)
    shared = chamber_slice(quarter, half, s, 1-s, 0)
    threshold = (2-3*s)/5

    def missing(r_hi, u_lo):
        return scale * (shared + chamber_slice(0, quarter, threshold, r_hi, u_lo))

    u_only = total - missing(1-s, 0)
    # The core is the union of U and the interiors where V has two
    # arbitrary short weights (or two arbitrary reflected short weights).
    core = total - missing(1-quarter, quarter-s)
    # This complement consists of shapes outside all dominance supports.
    forbidden = missing(half+s, half-2*s)
    assert total == 42
    assert u_only == q(1005295221, 25000000)
    assert core == q(1038774847179, 25600000000)
    assert forbidden == q(8570577, 12500000)
    return total, u_only, core, forbidden


@cache
def wing_monomial(i, j, k, second_term_vanishes):
    """Integral of z^i t^j s^k on either of the two parts of one wing."""
    # 0 < s < 1/4, 1/4 < t < 1/2-s, t < z < 3(1+s)/5.
    # The formula for a test changes at z = 1/2-s.
    split = half-s
    top = q(3, 5)*(1+s)

    def t_integral(n):
        return (split**(n+1)-quarter**(n+1))/(n+1)

    if second_term_vanishes:
        after_z_t = (top**(i+1)-split**(i+1))*t_integral(j)/(i+1)
    else:
        after_z_t = (split**(i+1)*t_integral(j)-t_integral(j+i+1))/(i+1)

    return sum(coeff * quarter**(power+k+1)/(power+k+1)
               for (power,), coeff in sp.Poly(after_z_t, s).terms())


def wing_dot(pair1, pair2):
    result = 0
    for second_term_vanishes, (left, right) in enumerate(zip(pair1, pair2)):
        result += sum(coeff * wing_monomial(*powers, second_term_vanishes)
                      for powers, coeff in (left * right).terms())
    return result


def wing_galerkin(core, degree):
    def poly(expression):
        return sp.Poly(expression, z, t, s)

    target = poly((z-t)*(z-s)*(t-s)/2)
    # A polynomial P(z,w) produces P(z,s+t) - P(t,s+z) on z+s<1/2
    # and P(z,s+t) on z+s>1/2. The chosen order is total degree <= degree.
    basis = []
    for i in range(degree+1):
        for j in range(degree+1-i):
            direct = z**i*(s+t)**j
            basis.append((poly(direct-t**i*(s+z)**j), poly(direct)))

    gram = sp.Matrix([[wing_dot(left, right) for right in basis] for left in basis])
    numerator = sp.Matrix([wing_dot((target, target), row) for row in basis])
    # Positive definiteness follows by restricting to an open set z+s>1/2.
    coefficients = gram.inv() * numerator
    assert gram * coefficients == numerator
    return core + 2*normalization*numerator.dot(coefficients)


def variance_loss():
    # On z+s >= 1/2 all tests are constant in s at fixed (z,w).
    # The right endpoint of the allowed s interval is w-1/4 in all cases.
    target = (z-w+s)*(z-s)*(w-2*s)/2
    right = w-quarter

    def piece(left, z_lo, z_hi):
        mean = sp.cancel(integrate(target, s, left, right)/(right-left))
        variance = integrate((target-mean)**2, s, left, right)
        return integrate(integrate(variance, z, z_lo, z_hi), w, quarter, half)

    integral = (piece(half-z, 1-quarter-w, half)
                + piece(0, half, q(3, 5))
                + piece((5*z-3)/3, q(3, 5), q(9, 20)+3*w/5))
    return 2*normalization*integral


def big_wing_gain():
    # At z >= 1/2 the second value of the trial function always vanishes.
    # Orthogonal projection at fixed z,w is integration in s divided by
    # the interval length. This height range does not couple to z < 1/2.
    target = (z-w+s)*(z-s)*(w-2*s)/2
    right = w-quarter

    def piece(left, z_lo, z_hi):
        mean = sp.cancel(integrate(target, s, left, right)/(right-left))
        square = (right-left)*mean**2
        return integrate(integrate(square, w, quarter+left, half), z, z_lo, z_hi)

    return 2*normalization*(piece(0, half, q(3, 5))
                            + piece((5*z-3)/3, q(3, 5), 1-quarter))


def small_wing_gain():
    # z=(1+U)/4, t=(1+V)/4, s=X/4, M=U+V+X. The two weights
    # are values of the same function of a vertex, H(M,U)-H(M,V).
    # A vertex below c=max(0,M-1) is pinned at zero.
    U, V, X, M = sp.symbols("U V X M")
    target = (U-V)*(1+U-X)*(1+V-X)
    edge = target.subs(X, M-U-V)
    top = M-U
    source = integrate(edge, V, 0, top)

    # Recover the potential on the unpinned triangle from its normal
    # equation by undetermined coefficients. A constant is immaterial.
    a, b, c3 = sp.symbols("a b c3")
    trial = a*U + b*U**2 + c3*U**3
    residual = sp.Poly(sp.cancel(
        (top*trial - integrate(trial.subs(U, V), V, 0, top) - source)/top), U)
    solution, = sp.solve(residual.all_coeffs(), (a, b, c3), dict=True)
    potential = trial.subs(solution)
    assert sp.simplify(potential - U*(3*U+1-2*M)) == 0

    cut = M-1
    # For M>1, use H=0 below cut and shift the solution above cut so the
    # omitted interval has mean zero. All free U satisfy M-U >= cut.
    shift = sp.cancel(-integrate(potential, U, 0, cut)/cut)
    pinned = potential+shift
    assert sp.simplify(shift-cut/2) == 0
    assert sp.expand(top*pinned
                     - integrate(pinned.subs(U, V), V, cut, top)
                     - source) == 0

    below = integrate(integrate(potential*source, U, 0, M), M, 0, 1)
    above = integrate(integrate(pinned*source, U, cut, 1), M, 1, 2)
    # Scale includes the reflection factor 2, target denominator 2,
    # cubic rescaling squared and volume rescaling.
    return q(normalization, 2*4**9)*(below+above)


if __name__ == "__main__":
    total, u_only, core, forbidden = shape_masses()
    variance = variance_loss()
    ceiling = total-forbidden-variance
    print("U-only optimum", u_only, float(u_only))
    print("Core mass", core, float(core))
    for degree in range(5):
        lower = wing_galerkin(core, degree)
        print("Wing potential degree", degree, "lower bound", lower, float(lower))
    assert lower == q(
        23984821608243066172033162671545209719723887786777088071224545688330557,
        581296697185280334635446507971739973732646976154770669127045120000000,
    )
    assert variance == q(10656627, 204800000)
    assert ceiling == q(1056315379929, 25600000000)
    print("Forbidden mass", forbidden, float(forbidden))
    print("Conditional variance over all single-value fibers", variance, float(variance))
    print("Upper bound before solving the normal equation", ceiling, float(ceiling))

    optimum = core + big_wing_gain() + small_wing_gain()
    assert lower < optimum < ceiling
    assert optimum == q(264076794201, 6400000000)
    print("Exact method optimum", optimum, float(optimum))
