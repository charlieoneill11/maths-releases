"""Checks for the section on marked tests and the spectral estimate.

1. The marked-profile identity h_{c_psi} = psi(x+y+z, x+y, x), by direct
   quadrature of the Pieri-kernel integral (eq:profile) for a test psi.
2. The local denominator factor of the Ramanujan inversion and the value
   of the four-edge Euler constant at the origin.
3. The Euler numerator of the shifted ternary-divisor series against a
   Hecke eigenform.
4. The exponent bookkeeping of the signed estimate.
6. The exponential-profile (continuous Gelfand--Tsetlin) identity.
5. mu(N_0) = 209/1024 by numerical quadrature.
7. mu(N_0) = 209/1024 exactly, by integrating 9! v^2 over a rational
   triangulation of the polytope N_0.

Run: python marked_spectral_checks.py
"""

from fractions import Fraction
from math import factorial

import numpy as np
import sympy as sp
from scipy import integrate

# ---------------------------------------------------------------------------
# 1. Marked profile identity.
# psi(r,k,x) is a smooth bump supported in r-1<k<r/2, 0<x<k/2 near a point.


def bump(t):
    out = np.zeros_like(t)
    inside = np.abs(t) < 1
    out[inside] = np.exp(-1.0 / (1.0 - t[inside] ** 2))
    return out


R0, K0, X0, RAD = 1.20, 0.555, 0.140, 0.030   # centre (r,k,x); support radius


def psi(r, k, x):
    return bump((r - R0) / RAD) * bump((k - K0) / RAD) * bump((x - X0) / RAD)


def m(r, k, u, h=1e-5):
    """m = -d psi / d(third slot), by a central difference."""
    return -(psi(r, k, u + h) - psi(r, k, u - h)) / (2 * h)


def c_marked(a1, a2, a3, h=2e-4):
    """c(a) = (d_u d_v f)(r,u,v) at (a1+a2+a3, a1, a2), f(r,u,v) = m(r,u+v,u)."""
    r = a1 + a2 + a3

    def f(u, v):
        return m(r, u + v, u)
    return (f(a1 + h, a2 + h) - f(a1 + h, a2 - h) - f(a1 - h, a2 + h) + f(a1 - h, a2 - h)) / (4 * h * h)


def kappa(x, y, z, c1, c2):
    lo = np.maximum.reduce([np.full_like(c1, y), c1 + c2 - y, c1, c2])
    hi = np.minimum(z, c1 + c2 - x)
    return np.clip(hi - lo, 0.0, None)


def profile(x, y, z, n=1400):
    r = x + y + z
    # c1,c2 range over a box containing the support of c (|c - centre| small).
    c1 = np.linspace(0.0, 0.5, n)
    c2 = np.linspace(0.0, 0.7, n)
    C1, C2 = np.meshgrid(c1, c2, indexing="ij")
    C3 = r - C1 - C2
    val = c_marked(C1, C2, C3) * kappa(x, y, z, C1, C2)
    return integrate.simpson(integrate.simpson(val, x=c2, axis=1), x=c1)


rng = np.random.default_rng(1)
worst = 0.0
for _ in range(6):
    r = R0 + RAD * rng.uniform(-0.6, 0.6)
    k = K0 + RAD * rng.uniform(-0.6, 0.6)
    x = X0 + RAD * rng.uniform(-0.6, 0.6)
    y, z = k - x, r - k
    lhs, rhs = profile(x, y, z), float(psi(np.array(r), np.array(k), np.array(x)))
    worst = max(worst, abs(lhs - rhs) / max(abs(rhs), 1e-3))
# A point off the dominant region (x+y>z) must give zero.
off = profile(0.30, 0.45, 0.50)
assert worst < 5e-3 and abs(off) < 1e-6, (worst, off)
print(f"marked profile identity: max relative error {worst:.1e}; off-support value {off:.1e}")

# ---------------------------------------------------------------------------
# 2. Local factors.
P, Y, A, B = sp.symbols("P Y alpha beta")
p = sp.Symbol("p", positive=True)
# Probability that p^e | D E with independent geometric valuations of
# parameters p^{-1-A}, p^{-1-B}; generating series of q-weighted coefficients.
Pa, Pb = p ** (-1 - A), p ** (-1 - B)
lhs = (1 - p * Y * (1 - Pa) * (1 - Pb) / ((1 - p * Pa * Y) * (1 - p * Pb * Y))) / (1 - p * Y)
rhs = (1 - p ** (-1 - A - B) * Y) / ((1 - p ** (-A) * Y) * (1 - p ** (-B) * Y))
assert sp.simplify(lhs - rhs) == 0
# Four-edge constant at the origin (m_0 = phi): both sides equal
# (1-P)^4 (1+4P+P^2); compared as power series in P to order 40.
ORDER = 40


def trunc(expr):
    poly = sp.Poly(sp.expand(expr), P)
    return sum(cf * P ** mon[0] for mon, cf in poly.terms() if mon[0] < ORDER)


target = trunc((1 - P) ** 4 * (1 + 4 * P + P ** 2))
left = (1 - P) ** 4 * (1 + (1 - P) * sum(P ** j * (1 + j * (1 - P)) ** 2 for j in range(1, ORDER + 2)))
right = (1 - P) ** 9 * sum(sp.binomial(j + 2, 2) ** 2 * P ** j for j in range(ORDER + 2))
for expr in (left, right):
    assert sp.expand(trunc(expr) - target) == 0
print("local denominator factor and four-edge constant: confirmed")

# ---------------------------------------------------------------------------
# 3. Euler numerator: sum_v h_v(z1,z2,z3) lambda(p^v) t^v
#    = [1 - e2 t^2 + lambda(p) e3 t^3] / prod_i (1 - alpha z_i t)(1 - beta z_i t),
#    with alpha beta = 1, lambda(p^v) = (alpha^{v+1}-beta^{v+1})/(alpha-beta).
z1, z2, z3, al, t = sp.symbols("z1 z2 z3 al t")
be = 1 / al
lam = lambda v: sp.cancel((al ** (v + 1) - be ** (v + 1)) / (al - be))
zs = (z1, z2, z3)
hv = [sp.expand(sum(z1 ** i * z2 ** j * z3 ** (v - i - j) for i in range(v + 1) for j in range(v + 1 - i))) for v in range(9)]
series_lhs = sp.expand(sum(hv[v] * lam(v) * t ** v for v in range(9)))
e2 = z1 * z2 + z1 * z3 + z2 * z3
e3 = z1 * z2 * z3
num = 1 - e2 * t ** 2 + lam(1) * e3 * t ** 3
den = sp.Mul(*[(1 - al * zi * t) * (1 - be * zi * t) for zi in zs])
DEG = 9
lhs_times_den = sp.Poly(sp.expand(series_lhs * sp.expand(den * al ** 3)), t)
num_poly = sp.Poly(sp.expand(num * al ** 3), t)
for v in range(DEG):
    assert sp.simplify(lhs_times_den.coeff_monomial(t ** v) - num_poly.coeff_monomial(t ** v)) == 0
print("Euler numerator 1 - e2 X^2 + lambda(p) e3 X^3: confirmed to order 8")

# ---------------------------------------------------------------------------
# 4. Exponent bookkeeping, with h = 1 - 1/r, s = k/r, t = x/r.
h, s, tt, r_, k_, x_ = sp.symbols("h s t r k x", positive=True)
Aexp, Nexp, Kexp = s - h, 3 * s - 1, s + ((s - h) - (3 * s - 1)) / 2
pexp = (1 + h) / 2 - s - tt
assert sp.simplify(tt + (Aexp + Nexp) / 2 - s + pexp) == 0          # D sqrt(AN)/Q = X^{-p}
assert sp.simplify(Kexp - Aexp - tt - pexp) == 0                     # K/(AD) = X^{p}
assert sp.simplify(Nexp - s - Aexp / 2 - ((3 * s + h) / 2 - 1)) == 0  # N/(Q sqrt A)
subs = {h: 1 - 1 / r_, s: k_ / r_, tt: x_ / r_}
assert sp.simplify(r_ * pexp.subs(subs) - ((r_ - k_) - x_ - sp.Rational(1, 2))) == 0
print("exponents: D sqrt(AN)/Q = X^-p, K/(AD) = X^p, r p = z - x - 1/2: confirmed")

# ---------------------------------------------------------------------------
# 6. Exponential profiles (lem:expprofile): the profile of exp(-u.a) equals
#    det[exp(-u_j lambda_i)] / ((u1-u2)(u1-u3)(u2-u3)) with lambda = (x,y,z),
#    and equals the sum of the three source residues of lem:polarlimit.
def h_exp(u, x, y, z):
    r = x + y + z
    def f(a, w, up):
        return np.exp(-u[0] * a - u[1] * (up + w - a) - u[2] * (r - up - w))
    lims = (y, z, lambda up: x, lambda up: y, lambda up, w: w, lambda up, w: up)
    re, _ = integrate.tplquad(lambda a, w, up: f(a, w, up).real, *lims, epsabs=1e-12)
    im, _ = integrate.tplquad(lambda a, w, up: f(a, w, up).imag, *lims, epsabs=1e-12)
    return re + 1j * im


def det_form(u, x, y, z):
    lam = (x, y, z)
    mat = np.array([[np.exp(-u[j] * lam[i]) for j in range(3)] for i in range(3)])
    return np.linalg.det(mat) / ((u[0] - u[1]) * (u[0] - u[2]) * (u[1] - u[2]))


def residue_sum(u, x, y, z):
    r, k, total = x + y + z, x + y, 0
    for i in range(3):
        j, l = [t for t in range(3) if t != i]
        e_i = (np.exp(-(u[j] - u[i]) * x - (u[l] - u[i]) * (k - x))
               - np.exp(-(u[j] - u[i]) * (k - x) - (u[l] - u[i]) * x)) / (u[j] - u[l])
        total += np.exp(-r * u[i]) * e_i / ((u[j] - u[i]) * (u[l] - u[i]))
    return total


rng6 = np.random.default_rng(3)
for _ in range(3):
    u = 3j * rng6.normal(size=3) + 0.5 * rng6.normal(size=3)
    x, y, z = sorted(rng6.uniform(0, 1, 3))
    a, b, c = h_exp(u, x, y, z), det_form(u, x, y, z), residue_sum(u, x, y, z)
    assert abs(a - b) < 1e-9 and abs(b - c) < 1e-12, (a, b, c)
print("exponential profile = determinant formula = residue sum: confirmed")

# ---------------------------------------------------------------------------
# 5. mu(N_0), N_0 = {1<r<3/2, x+y>1/2, z-x<1/2} in coordinates (x,k,z).
NINE = factorial(9)


def dens(z, x, k):
    return NINE / 4 * (z - k + x) ** 2 * (z - x) ** 2 * (k - 2 * x) ** 2


def z_lo(x, k):
    return max(k - x, 1 - k)


def z_hi(x, k):
    return min(1.0, 1.5 - k, x + 0.5)


zz, xx, kk = sp.symbols("zz xx kk")
Fz = sp.lambdify((zz, xx, kk), sp.integrate(sp.expand(NINE / 4 * (zz - kk + xx) ** 2 * (zz - xx) ** 2 * (kk - 2 * xx) ** 2), zz))


def after_z(x, k):
    lo, hi = z_lo(x, k), z_hi(x, k)
    return Fz(hi, x, k) - Fz(lo, x, k) if hi > lo else 0.0


val, err = integrate.dblquad(lambda x, k: after_z(x, k), 0.5, 1.0, 0.0, lambda k: k / 2,
                             epsabs=1e-13, epsrel=1e-12)
assert abs(val - 209 / 1024) < 1e-9, val
print(f"mu(N_0) = {val:.12f}  (209/1024 = {209/1024:.12f})")
print("mu(S_3 u {z-x>1/2}) = 42 - 209/512 =", Fraction(42) - Fraction(209, 512),
      float(Fraction(42) - Fraction(209, 512)))

# ---------------------------------------------------------------------------
# 7. mu(N_0) exactly: N_0 is a convex polytope; integrate 9! v^2 exactly over
#    a triangulation of it, with rational vertices.
from itertools import combinations

from scipy.spatial import Delaunay

HALF, THREE_HALVES = sp.Rational(1, 2), sp.Rational(3, 2)
# inequalities a.(x,y,z) <= b
N0_INEQ = [((-1, 0, 0), 0), ((1, -1, 0), 0), ((0, 1, -1), 0), ((0, 0, 1), 1),
           ((-1, -1, -1), -1), ((1, 1, 1), THREE_HALVES), ((-1, -1, 0), -HALF),
           ((-1, 0, 1), HALF)]
verts = set()
for (a1, b1), (a2, b2), (a3, b3) in combinations(N0_INEQ, 3):
    A = sp.Matrix([a1, a2, a3])
    if A.det() == 0:
        continue
    p = A.LUsolve(sp.Matrix([b1, b2, b3]))
    if all(sum(ai * pi for ai, pi in zip(a, p)) <= b for a, b in N0_INEQ):
        verts.add(tuple(p))
verts = sorted(verts)
X, Y, Z = sp.symbols("X Y Z")
U1, U2, U3 = sp.symbols("U1 U2 U3")
dens_exact = sp.Integer(NINE) / 4 * ((Z - Y) * (Z - X) * (Y - X)) ** 2
mu_N0 = sp.Integer(0)
for simplex in Delaunay(np.array([[float(c) for c in v] for v in verts])).simplices:
    V = [sp.Matrix(verts[i]) for i in simplex]
    Jac = sp.Matrix.hstack(V[1] - V[0], V[2] - V[0], V[3] - V[0])
    pt = V[0] + Jac * sp.Matrix([U1, U2, U3])
    g = sp.expand(dens_exact.subs({X: pt[0], Y: pt[1], Z: pt[2]}))
    inner = sp.integrate(sp.integrate(sp.integrate(g, (U3, 0, 1 - U1 - U2)), (U2, 0, 1 - U1)), (U1, 0, 1))
    mu_N0 += abs(Jac.det()) * inner
assert mu_N0 == sp.Rational(209, 1024), mu_N0
print("mu(N_0) exactly by triangulation:", mu_N0)
