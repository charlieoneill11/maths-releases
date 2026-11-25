r"""Check of the residue identity used for unequal-length same-side tests.

For the V-numerator with scaled shifts sigma = (0,0,0,-z), the principal-character
residues in Section 4 of the paper produce the contour integral

    S(x,y) = (1/2 pi i) \oint e^v F(x,v) F(y,v) / Q(v) dv,
    Q(u) = u^3 (u - z),   F(x,v) = inverse Laplace_{u->x} of (u - v)/Q(u).

We verify, as an exact identity of closed-form expressions in (x, y, z), that

    exp(-z/2) S(x,y) = K_{exp(z.)}(x,y)      (0 < x <= y, x + y < 1),

where K_p is the Schur numerator kernel (eq. Kkernel of the paper); by the
Hermite--Genocchi formula, E exp(z sum c_i X_i) = 6 z^{-3} times the third divided
difference of exp(z.) at c_0..c_3. Both sides are entire in z, so comparing
z-derivatives at 0 gives the kernel K_p for every polynomial p.
Run: python unequal_v_kernel_check.py
"""
import random

import sympy as sp

x, y, u, v, z, w, t = sp.symbols("x y u v z w t", positive=True)


def inverse_laplace(expr):
    """Inverse Laplace transform u -> t of a rational function with poles at 0 and z."""
    out = 0
    for term in sp.Add.make_args(sp.apart(sp.together(expr), u)):
        num, den = sp.fraction(sp.factor(term))
        poly = sp.Poly(den, u)
        (root, mult), = sp.roots(poly).items()
        coeff = sp.simplify(num / poly.LC())
        assert not coeff.has(u)
        out += coeff * t**(mult - 1) / sp.factorial(mult - 1) * sp.exp(root * t)
    return out


# Schur side: K_{exp(z.)}(x,y) = (1/(2 z^3)) int_0^x sum_i (-1)^i Vdm(rho without i) e^{z(rho_i-1/2)} dw.
rho = [1, x + y - w, w, 0]
total = 0
for i in range(4):
    rest = [rho[k] for k in range(4) if k != i]
    vdm = sp.prod([rest[a] - rest[b] for a in range(3) for b in range(a + 1, 3)])
    total += (-1)**i * vdm * sp.exp(z * (rho[i] - sp.Rational(1, 2)))
schur = sp.integrate(sp.expand(total), (w, 0, x)) / (2 * z**3)

# Arithmetic side: residues of the contour integral at v = 0 and v = z.
Q = lambda s: s**3 * (s - z)
F = inverse_laplace((u - v) / Q(u))
integrand = sp.exp(v) * F.subs(t, x) * F.subs(t, y) / Q(v)
residue = sp.residue(integrand, v, 0) + sp.residue(integrand, v, z)

difference = sp.simplify(sp.expand(sp.powsimp(sp.expand(sp.exp(-z / 2) * residue - schur))))
assert difference == 0, difference
rng = random.Random(7)
for _ in range(5):
    point = {x: sp.Rational(rng.randint(1, 20), 100), z: sp.Rational(rng.randint(-30, 30), 7)}
    point[y] = point[x] + sp.Rational(rng.randint(0, 20), 100)
    a, b = sp.N((sp.exp(-z / 2) * residue).subs(point), 40), sp.N(schur.subs(point), 40)
    assert abs(a - b) < 1e-35 * (1 + abs(b))
print("exp(-z/2) S(x,y) = K_{exp(z.)}(x,y) identically; unequal-length numerator kernel confirmed.")
