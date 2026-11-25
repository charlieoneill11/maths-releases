"""Checks for the balanced row (paper, Section "The balanced row").

Run: python3 balanced_row_checks.py   (needs sympy, numpy, scipy)

1. The four-variable Schur identity
       sum_{max(A,B)<=j<=A+B} s_{(N,j,A+B-j,0)}(X_1..X_4)
     = sum_i X_i^{N+3} h_A(X_{!=i}) h_B(X_{!=i}) / prod_{l!=i}(X_i-X_l)
   for small N, A, B with A+B<=N, in exact rational arithmetic.
2. The local factor of the four-shift principal series at zero shifts equals
   (1+4X+X^2)/(1-X)^6, so that after removing ten net polar factors it is
   (1-X)^4(1+4X+X^2), the local factor of a_3.
3. First-order factorisation (Lemma "Euler product" (i)). As polynomials in
   X=1/p, with coefficients Laurent polynomials in p^{-omega}, p^{-v_i},
   p^{-w} and p^{-alpha_k}, the local factor S_p and the local factor of the
   predicted zeta quotient agree in degrees 0 and 1 (exact, symbolic); their
   degree-2 terms differ, as expected. A numerical evaluation of the ratio
   at p=101 and p=409, at one point with all real parts in [-1/20,1/20],
   is reported as well (floating point).
4. Jacobi--Trudi synthesis: the profile of (d_z-d_y)(d_z-d_x)(d_y-d_x)psi,
   as a function of (a_1,a_2,a_3)=(x,y,z), equals psi (quadrature).
5. Kernel identity: for a with a_1+a_2<1 the profile kernel of e^{-u.a},
   K(a) = int h_{e^{-u.a}}(x,y,r-x-y) kappa(x,y,r-x-y;a) dx dy (r=|a|),
   equals (1/2 pi i) int_{(C)} e^{U(1-a_3)} S(u_1,u_2,u_3,U;a_1,a_2) dU.
6. The exponent range: on a grid of the parameter region the best of the
   three discrepancy exponents is below one, with the margin reported.
7. The measure C_0 = 42 - 2(mu(N_0) - mu(N_0 cap D)).
"""
import itertools
import cmath
import math
from fractions import Fraction

import numpy as np
import sympy as sp
from scipy import integrate

rng = np.random.default_rng(1)

# ---------------------------------------------------------------- 1
def schur(lam, xs):
    n = len(xs)
    lam = list(lam) + [0] * (n - len(lam))
    num = sp.Matrix(n, n, lambda i, j: xs[i] ** (lam[j] + n - 1 - j))
    den = sp.Matrix(n, n, lambda i, j: xs[i] ** (n - 1 - j))
    return sp.nsimplify(num.det() / den.det())


def h_complete(A, ys):
    tot = 0
    for t in itertools.product(range(A + 1), repeat=len(ys) - 1):
        if sum(t) <= A:
            ex = list(t) + [A - sum(t)]
            term = 1
            for y, e in zip(ys, ex):
                term *= y ** e
            tot += term
    return tot


X = [sp.Rational(2, 7), sp.Rational(-3, 5), sp.Rational(5, 11), sp.Rational(7, 3)]
for N, A, B in [(4, 1, 2), (5, 2, 2), (5, 0, 3), (6, 3, 3), (6, 1, 4)]:
    lhs = sum(schur((N, j, A + B - j, 0), X) for j in range(max(A, B), A + B + 1))
    rhs = 0
    for i in range(4):
        rest = [X[l] for l in range(4) if l != i]
        den = 1
        for l in range(4):
            if l != i:
                den *= X[i] - X[l]
        rhs += X[i] ** (N + 3) * h_complete(A, rest) * h_complete(B, rest) / den
    assert sp.simplify(lhs - rhs) == 0, (N, A, B)
print("1. four-variable Schur identity: exact for 5 cases")

# ---------------------------------------------------------------- 2
Xs = sp.symbols("X")


def f_loc(a, j, m, x):
    if a <= j + m:
        return 1
    if a == j + m + 1:
        return -x / (1 - x)
    return 0


R = 18
ser = 0
for m in range(R):
    for j in range(R - m):
        for a1 in range(m + j + 2):
            for a2 in range(m + j + 2 - a1):
                ser += sp.binomial(m + 2, 2) * Xs ** (m + j) * f_loc(a1 + a2, j, m, Xs)
target = (1 + 4 * Xs + Xs ** 2) / (1 - Xs) ** 6
diff = sp.series(ser - target, Xs, 0, 17).removeO()
assert sp.expand(diff) == 0
assert sp.expand((1 - Xs) ** 10 * target - (1 - Xs) ** 4 * (1 + 4 * Xs + Xs ** 2)) == 0
print("2. zero-shift local factor = (1+4X+X^2)/(1-X)^6 (to order 16)")

# ---------------------------------------------------------------- 3
def local_factor(p, om, v1, v2, w, us, M=12):
    """Local factor at p of sum_{n,n1,n2,J} b_u(n) n^{-1-om} n1^{om-v1} n2^{om-v2}
    J^{-1-om-w} f(v(n1 n2), v(J), v(n)), divided by prod_k (1-p^{-1-om-u_k})^{-1}."""
    Y = p ** (-1 - om)
    T1, T2 = p ** (om - v1), p ** (om - v2)
    Rr = p ** (-1 - om - w)
    # b_u(p^m): coefficients of prod_k (1 - p^{-u_k} t)^{-1}
    B = [0j] * (3 * M)
    for e in itertools.product(range(3 * M), repeat=3):
        if sum(e) < 3 * M:
            B[sum(e)] += cmath.exp(-sum(ek * uk for ek, uk in zip(e, us)) * math.log(p))
    tot = 0j
    for m in range(M):
        for j in range(M - m):
            for a1 in range(m + j + 2):
                for a2 in range(m + j + 2 - a1):
                    f = f_loc(a1 + a2, j, m, 1 / p)
                    if f:
                        tot += B[m] * Y ** m * T1 ** a1 * T2 ** a2 * Rr ** j * f
    for uk in us:
        tot *= 1 - p ** (-1 - om - uk)
    return tot


def predicted(p, om, v1, v2, w, us):
    z = lambda s: 1 / (1 - p ** (-s))
    val = 1
    for uk in us:
        for v in (v1, v2):
            val *= z(1 + v + uk)
    val *= z(1 + om + w)
    for v in (v1, v2):
        val *= z(1 + w + v) / z(1 + v - om)
    return val


om, v1, v2, w = 0.03 + 0.05j, 0.05 - 0.02j, 0.04 + 0.04j, 0.05 + 0.01j  # real parts in [-1/20, 1/20]
us = [0.01j, -0.02j, 0.035j]
errs = {}
for p in (101, 409):
    errs[p] = abs(local_factor(p, om, v1, v2, w, us) / predicted(p, om, v1, v2, w, us) - 1)
ratio = errs[101] / errs[409]
assert 8 < ratio < 30, (errs, ratio)  # p^{-2} scaling predicts (409/101)^2 ~ 16.4
print("3. local factor / zeta quotient - 1 at p=101, 409:", errs, "ratio", round(ratio, 2))


def formal_first_order():
    """Exact check: S_p and the zeta-quotient local factor agree through degree 1 in X=1/p."""
    x, O, V1, V2, Wv = sp.symbols("X O V1 V2 Wv")  # O=p^-omega, Vi=p^-v_i, Wv=p^-w
    A = sp.symbols("A1:4")  # A_k = p^-alpha_k
    deg = 2  # keep terms of X-degree <= deg

    def trunc(e):
        e = sp.expand(e)
        return sum(e.coeff(x, d) * x ** d for d in range(deg + 1))

    def h(m):
        return sum(A[0] ** i * A[1] ** j * A[2] ** (m - i - j)
                   for i in range(m + 1) for j in range(m + 1 - i))

    geo = sum(x ** e for e in range(1, deg + 1))  # x/(1-x) to degree deg
    Sp = 0
    for m in range(deg + 1):
        for j in range(deg + 1 - m):
            for a1 in range(m + j + 2):
                for a2 in range(m + j + 2 - a1):
                    a = a1 + a2
                    if a <= j + m:
                        f = 1
                    elif a == j + m + 1:
                        f = -geo
                    else:
                        continue
                    Sp += h(m) * (x * O) ** m * (V1 / O) ** a1 * (V2 / O) ** a2 * (x * O * Wv) ** j * f
    for k in range(3):
        Sp *= 1 - x * O * A[k]
    Sp = trunc(Sp)

    def zinv_series(mono):  # (1 - x*mono)^{-1} truncated
        return sum((x * mono) ** e for e in range(deg + 1))

    pred = 1
    for Ak in A:
        for Vi in (V1, V2):
            pred = trunc(pred * zinv_series(Vi * Ak))
    pred = trunc(pred * zinv_series(O * Wv))
    for Vi in (V1, V2):
        pred = trunc(pred * zinv_series(Wv * Vi) * (1 - x * Vi / O))
    diff = sp.expand(Sp - pred)
    assert sp.simplify(diff.coeff(x, 0)) == 0 and sp.simplify(diff.coeff(x, 1)) == 0
    assert sp.simplify(diff.coeff(x, 2)) != 0
    return sp.expand(Sp.coeff(x, 1))


F1 = formal_first_order()
print("3. formal check: S_p and the zeta quotient agree in degrees 0 and 1 in 1/p;",
      "degree-1 term has", len(sp.Add.make_args(F1)), "monomials")

# ---------------------------------------------------------------- 4
xs_, ys_, zs_ = sp.symbols("x y z")
centre = (sp.Rational(22, 100), sp.Rational(30, 100), sp.Rational(49, 100))
rad = sp.Rational(1, 25)
q = ((xs_ - centre[0]) ** 2 + (ys_ - centre[1]) ** 2 + (zs_ - centre[2]) ** 2) / rad ** 2
bump = sp.exp(-1 / (1 - q))
G_inner = sp.diff(bump, ys_) - sp.diff(bump, xs_)
G_mid = sp.diff(G_inner, zs_) - sp.diff(G_inner, xs_)
G_full = sp.diff(G_mid, zs_) - sp.diff(G_mid, ys_)
G_num = sp.lambdify((xs_, ys_, zs_), G_full, "numpy")
cx, cy, cz, rr = 0.22, 0.30, 0.49, 0.04  # ball compactly inside the chamber


def G(a1, a2, a3):
    qq = ((a1 - cx) ** 2 + (a2 - cy) ** 2 + (a3 - cz) ** 2) / rr ** 2
    out = np.zeros_like(qq)
    mask = qq < 1 - 1e-9
    out[mask] = G_num(a1[mask], a2[mask], a3[mask])
    return out


def psi(x, y, z):
    qq = ((x - cx) ** 2 + (y - cy) ** 2 + (z - cz) ** 2) / rr ** 2
    return math.exp(-1 / (1 - qq)) if qq < 1 else 0.0


def kappa(x, y, z, c1, c2):
    return np.maximum(np.minimum(z, c1 + c2 - x) - np.maximum.reduce([np.full_like(c1, y), c1 + c2 - y, c1, c2]), 0)


def profile(F, x, y, z, n=1200):
    r = x + y + z
    # integrate over the box where F can be non-zero
    c1 = np.linspace(cx - rr, cx + rr, n)
    c2 = np.linspace(cy - rr, cy + rr, n)
    C1, C2 = np.meshgrid(c1, c2, indexing="ij")
    vals = F(C1, C2, r - C1 - C2) * kappa(x, y, z, C1, C2)
    return integrate.trapezoid(integrate.trapezoid(vals, c2, axis=1), c1)


for pt in [(0.22, 0.30, 0.49), (0.23, 0.31, 0.48), (0.24, 0.30, 0.50)]:
    hv, pv = profile(G, *pt), psi(*pt)
    assert abs(hv - pv) < 2e-3 * max(1e-3, abs(pv)) + 1e-6, (pt, hv, pv)
print("4. profile of the Jacobi-Trudi weight equals psi at 3 points")

# ---------------------------------------------------------------- 5
u = np.array([0.4j, -0.9j, 1.3j])


def h_exp(x, y, z):
    lam = np.array([x, y, z])
    M = np.exp(-np.outer(lam, u))
    den = (u[0] - u[1]) * (u[0] - u[2]) * (u[1] - u[2])
    return np.linalg.det(M) / den


def K_profile(a, n=500):
    r = sum(a)
    c1, c2 = a[0], a[1]
    # region of (x,y): kappa>0 needs x<y<z, x+y<c1+c2 ...
    xs = np.linspace(0, r / 3, n)
    ys = np.linspace(0, r / 2, n)
    tot = 0
    Xg, Yg = np.meshgrid(xs, ys, indexing="ij")
    Zg = r - Xg - Yg
    kap = np.maximum(np.minimum(Zg, c1 + c2 - Xg) - np.maximum.reduce([Yg, c1 + c2 - Yg, np.full_like(Xg, c1), np.full_like(Xg, c2)]), 0)
    kap[(Xg >= Yg) | (Yg >= Zg) | (Zg >= 1)] = 0
    lamb = np.stack([Xg, Yg, Zg], -1)
    M = np.exp(-lamb[..., :, None] * u[None, None, None, :])
    den = (u[0] - u[1]) * (u[0] - u[2]) * (u[1] - u[2])
    hv = np.linalg.det(M) / den
    vals = hv * kap
    return integrate.trapezoid(integrate.trapezoid(vals, ys, axis=1), xs)


def S_kernel(sig, a, b):
    tot = 0
    for k in range(4):
        others = [sig[l] for l in range(4) if l != k]
        def F(x):
            s = 0
            for l in range(3):
                rest = [others[m] for m in range(3) if m != l]
                s += np.exp(-others[l] * x) / ((rest[0] - others[l]) * (rest[1] - others[l]))
            return s
        den = np.prod([sig[l] - sig[k] for l in range(4) if l != k])
        tot += np.exp(-sig[k]) * F(a) * F(b) / den
    return tot


def K_arith(a, C=2.0, Ymax=4000.0, n=400001):
    t = np.linspace(-Ymax, Ymax, n)
    U = C + 1j * t
    vals = np.array([np.exp(Uv * (1 - a[2])) * S_kernel([u[0], u[1], u[2], Uv], a[0], a[1]) for Uv in U])
    return integrate.trapezoid(vals, t) / (2 * np.pi)


for a in [(0.26, 0.31, 0.47), (0.2, 0.33, 0.6)]:
    kp, ka = K_profile(a), K_arith(a)
    rel = abs(kp - ka) / abs(kp)
    assert rel < 2e-3, (a, kp, ka)
    print("5. kernel at", a, ": profile", kp, " residue formula", ka, " relative difference", rel)

# ---------------------------------------------------------------- 6
def best_exponent(k, r, a, b, c):
    k = max(k, 0.5)
    sides = (a, b, c)
    best = 10.0
    for U_, V_, W_ in itertools.permutations(sides):
        e1 = k + max(5 * k / 6, k / 4 + (U_ + V_) / 2, k / 2 + W_ / 2)
        e2 = k + k / 2 + U_
        e3 = k + 3 * U_ / 4 + V_ / 2 + max(W_, U_) / 4 + max(0.0, V_ / 2 - k / 4)
        best = min(best, e1, e2, e3)
    return best


worst = 0.0
for r in np.linspace(1.0005, 15 / 14 - 1e-4, 25):
    kmax = (18 - 7 * r) / 21
    for k in np.linspace(0.3, kmax - 1e-4, 25):
        for a in np.linspace(0, r / 3, 30):
            for b in np.linspace(a, (r - a) / 2, 30):
                worst = max(worst, best_exponent(k, r, a, b, r - a - b))
assert worst < 1
print("6. largest best-exponent on the grid:", round(worst, 5), "< 1")

# ---------------------------------------------------------------- 7
muN0 = Fraction(209, 1024)
muN0D = Fraction(62748701, 30991570176)
C0 = 42 - 2 * (muN0 - muN0D)
assert C0 == Fraction(2578241177999, 61983140352)
print("7. C_0 =", C0, "=", float(C0))
