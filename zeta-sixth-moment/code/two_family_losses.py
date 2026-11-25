"""Exact check of every number in Section 3 of the paper (two-family optimum).

Each quantity is computed directly from the formula printed in the paper, in
rational arithmetic, independently of optimization.py (which organises the
same optimum differently). Run: python two_family_losses.py
"""

from math import factorial

import sympy as sp

x, y, z, t, d, S, u, w, m, c, h, ell = sp.symbols("x y z t d S u w m c h ell")
Q = sp.Rational
NINE = factorial(9)


def I(expr, var, lo, hi):
    return sp.expand(sp.integrate(sp.expand(expr), (var, lo, hi)))


# Lemma 2.1: mu(Omega) = 42, via Heine's identity and the 3x3 Hilbert matrix.
hilbert = sp.Matrix(3, 3, lambda i, j: Q(1, i + j + 1))
assert hilbert.det() == Q(1, 2160)
vsq = (Q(1, 2) * (z - y) * (z - x) * (y - x))**2
mass = NINE * I(I(I(vsq, x, 0, y), y, 0, z), z, 0, 1)
assert mass == 42 == NINE * Q(1, 4) * 6 * hilbert.det() / 6
print("mu(Omega) =", mass)

# Loss L0 = mu(B), coordinates x, rho = 1 - z, t = y - x, d = 1 - rho - x.
rho = sp.Symbol("rho")
dens = t**2 * (d - t)**2 * d**2          # equals 4 v^2
dens = dens.subs(d, 1 - rho - x)
first = I(I(I(dens, t, Q(1, 2) - 2 * x, 1 - rho - x), rho, (2 - 3 * x) / 5, Q(1, 2) + x), x, 0, Q(1, 4))
second = I(I(I(dens, t, 0, 1 - rho - x), rho, x, 1 - x), x, Q(1, 4), Q(1, 2))
L0_parts = (Q(NINE, 2) * first, Q(NINE, 2) * second)
assert L0_parts == (Q(60361491, 100000000), Q(21, 256))
L0 = sum(L0_parts)
assert L0 == Q(8570577, 12500000)
print("L0 =", L0, float(L0))

# Loss L1: conditional variance on W with z >= 1/2, fibre l < x < h = S - 1/4.
P = Q(1, 2) * (z - S + x) * (z - x) * (S - 2 * x)


def variance(lo):
    hi = S - Q(1, 4)
    a = I(P**2, x, lo, hi)
    b = I(P, x, lo, hi)
    return sp.cancel(a - b**2 / (hi - lo))


v0 = variance(0)                         # 1/2 < z < 3/5, l = 0
v1 = variance((5 * z - 3) / 3)           # 3/5 < z < 3/4
part0 = 2 * NINE * sp.integrate(sp.integrate(v0, (S, Q(1, 4), Q(1, 2))), (z, Q(1, 2), Q(3, 5)))
part1 = 2 * NINE * sp.integrate(sp.integrate(v1, (S, Q(1, 4) + (5 * z - 3) / 3, Q(1, 2))), (z, Q(3, 5), Q(3, 4)))
part0, part1 = sp.nsimplify(sp.simplify(part0)), sp.nsimplify(sp.simplify(part1))
assert part0 == Q(588879, 25600000) and part1 == Q(1114119, 40960000)
L1 = part0 + part1
print("L1 =", part0, "+", part1, "=", L1, float(L1))

# Loss L2: the normal equation (3.x) and its solution on the small region.
v_ = sp.Symbol("v")
dm = (u - v_) * (1 + u - (m - u - v_)) * (1 + v_ - (m - u - v_))
bm = I(dm, v_, 0, m - u)
assert sp.expand(bm - (m - u) / 2 * (-2 * m * u - m + 4 * u**2 + 3 * u)) == 0
f = 3 * u**2 + (1 - 2 * m) * u
for cc, label in ((0, "m<=1"), (m - 1, "m>1")):
    fm = f + cc / 2
    lhs = (m - u) * fm - I(fm.subs(u, v_), v_, cc, m - u)
    assert sp.expand(lhs - bm) == 0, label
    if cc != 0:  # the omitted interval (0,c) has mean zero for the unpinned polynomial + c/2
        assert sp.expand(I(fm.subs(u, v_), v_, 0, cc)) == 0
target = I(I(I(dm.subs(m, u + v_ + w)**2, w, 0, 1 - v_), v_, 0, u), u, 0, 1)
assert target == Q(104, 945)
captured = I(I(f * bm, u, 0, m), m, 0, 1) + I(I((f + (m - 1) / 2) * bm, u, m - 1, 1), m, 1, 2)
assert captured == Q(77, 720)
L2 = Q(NINE, 2 * 4**9) * (target - captured)
assert L2 == Q(141, 65536)
print("L2 =", L2, float(L2))

Cstar = 42 - L0 - L1 - L2
assert Cstar == Q(264076794201, 6400000000)
print("C* = 42 - L0 - L1 - L2 =", Cstar, float(Cstar))

# Remark on derivative degree four: the jump of d/dz of the conditional mean at z = 3/5.
hh = Q(1, 8)
Pz = P.subs({S: Q(3, 8), z: Q(3, 5)})
jump = Q(5, 3) / hh * (I(Pz, x, 0, hh) / hh - Pz.subs(x, 0))
assert jump == Q(-83, 960)
print("kink of the optimal mean at z = 3/5, S = 3/8:", jump)
print("All two-family constants confirmed.")


# Section 4: the low slab E = {x<y<z, x+y>1/2, x+y+z<1} (so 1/4<y<1/2, z<1/2)
# and the coefficient mu(S_3) = 42 - L0 + 2 mu(E) of the third family.
def E_inner(x_lo, x_hi):
    return I(I(vsq, z, y, 1 - x - y), x, x_lo, x_hi)


E_mass = NINE * (I(E_inner(Q(1, 2) - y, y), y, Q(1, 4), Q(1, 3))
                 + I(E_inner(Q(1, 2) - y, 1 - 2 * y), y, Q(1, 3), Q(1, 2)))
assert E_mass == Q(1, 1024)
S3 = 42 - L0 + 2 * E_mass
assert S3 == Q(8263261393, 200000000)
print("mu(E) =", E_mass, "; mu(S_3) = 42 - L0 + 1/512 =", S3, float(S3))
