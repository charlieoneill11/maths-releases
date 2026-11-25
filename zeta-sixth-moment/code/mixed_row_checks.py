"""Exact checks for the extended mixed row and the coefficient 41.6406029094...

Section 1. The support mass.  Every integration cell of the extended region is
           integrated exactly, by iterated polynomial antiderivatives and,
           independently, by exact vertex enumeration and triangulation into
           tetrahedra.  Each cell is checked to lie in N0, inside the mark range
           of the estimate that covers it, and to meet neither the balanced
           region R nor the other cells in positive measure.  The cells of each
           stage are checked to exhaust the newly covered set, computed directly
           from the mark ranges.  The final coefficient is compared with the
           exact fraction.
Section 2. The case analysis.  For each of the 84 + 84 reciprocal-completion
           branches and the 672 + 672 + 784 represented-level branches, the
           stored multipliers in mixed_row_certificates.json are checked to be
           nonnegative rationals whose combination of the branch hypotheses
           equals -gap or -1 exactly.
Section 3. The variance lower limit (C - 2)/2.
Section 4. The ceiling of prop:ceiling with the mixed-row region added to its
           list: the release value is recomputed, then the increment from F+.
Section 5. The prose case analyses lem:cases (i)-(ii) (all marks for s < 1/10;
           beta < (3-21s)/2 for 1/10 <= s < 1/8), by exact certificates at the
           nodes of the disjunction tree (13122 and 76545 branches).
Section 6. Every affine identity quoted in lem:degrees through lem:cases, checked
           by expansion, and the coefficient of rem:fallback (the mark ranges
           of the completion bands, without the represented-level estimate).

Run with assertions enabled:  python3 -B mixed_row_checks.py
The script exits with status 0 only if every check passes.
"""
import json
import os
import sys
from fractions import Fraction as Fr
from itertools import combinations, product
from math import factorial

import sympy as sp


def check(cond, msg):
    """Fail loudly; independent of the -O flag."""
    if not cond:
        raise AssertionError(msg)


HERE = os.path.dirname(os.path.abspath(__file__))
HALF = Fr(1, 2)
FINAL = Fr(112666832560750258461501594014215737455802061,
           2705696476246250148185796472625838239963136)
C0 = Fr(2578241177999, 61983140352)

# ---------------------------------------------------------------- Section 1
K, X, Z = sp.symbols('k x z')
DENS = sp.Rational(factorial(9), 4) * (K - 2*X)**2 * (Z - X)**2 * (Z - K + X)**2  # 9! v^2


def cons(ak, ax, az, c):
    """The open half-space ak*k + ax*x + az*z + c > 0."""
    return (Fr(ak), Fr(ax), Fr(az), Fr(c))


def val(c, p):
    return c[0]*p[0] + c[1]*p[1] + c[2]*p[2] + c[3]


def solve3(rows, rhs):
    (a, b, c), (d, e, f), (g, h, i) = rows
    det = a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)
    if det == 0:
        return None
    r0, r1, r2 = rhs
    return ((r0*(e*i - f*h) - b*(r1*i - f*r2) + c*(r1*h - e*r2)) / det,
            (a*(r1*i - f*r2) - r0*(d*i - f*g) + c*(d*r2 - r1*g)) / det,
            (a*(e*r2 - r1*h) - b*(d*r2 - r1*g) + r0*(d*h - e*g)) / det)


def vertices(P):
    out = set()
    for c1, c2, c3 in combinations(P, 3):
        p = solve3([c1[:3], c2[:3], c3[:3]], [-c1[3], -c2[3], -c3[3]])
        if p is not None and all(val(c, p) >= 0 for c in P):
            out.add(p)
    return sorted(out)


def rat(q):
    return sp.Rational(q.numerator, q.denominator)


def mass_by_slicing(P):
    """Iterated antiderivatives, z innermost, then x, then k."""
    vs = vertices(P)
    if len(vs) < 4:
        return Fr(0)
    ks = sorted(set(v[0] for v in vs))
    total = Fr(0)
    for ka, kb in zip(ks, ks[1:]):
        total += _slab(P, ka, kb)
    return total


def _slab(P, ka, kb):
    km = (ka + kb) / 2
    xs = {}
    for c1, c2 in combinations(P, 2):
        det = c1[1]*c2[2] - c1[2]*c2[1]
        if det == 0:
            continue
        x1 = (-c1[0]*c2[2] + c1[2]*c2[0]) / det
        x0 = (-c1[3]*c2[2] + c1[2]*c2[3]) / det
        z1 = (-c1[1]*c2[0] + c1[0]*c2[1]) / det
        z0 = (-c1[1]*c2[3] + c1[3]*c2[1]) / det
        pt = (km, x0 + x1*km, z0 + z1*km)
        if all(val(c, pt) >= 0 for c in P):
            xs.setdefault(pt[1], (x0, x1))
    funcs = [xs[key] for key in sorted(xs)]
    cuts = set()
    for (a0, a1), (b0, b1) in combinations(funcs, 2):
        if a1 != b1:
            kc = (b0 - a0) / (a1 - b1)
            if ka < kc < kb:
                cuts.add(kc)
    if cuts:
        pts = [ka] + sorted(cuts) + [kb]
        return sum((_slab(P, a, b) for a, b in zip(pts, pts[1:])), Fr(0))
    total = sp.Integer(0)
    for xa, xb in zip(funcs, funcs[1:]):
        xm = (xa[0] + xa[1]*km + xb[0] + xb[1]*km) / 2
        lows, ups = [], []
        for c in P:
            if c[2] == 0:
                continue
            bnd = (-c[0]/c[2], -c[1]/c[2], -c[3]/c[2])
            (lows if c[2] > 0 else ups).append((bnd[0]*km + bnd[1]*xm + bnd[2], bnd))
        lo, hi = max(lows)[1], min(ups)[1]
        zl = rat(lo[0])*K + rat(lo[1])*X + rat(lo[2])
        zh = rat(hi[0])*K + rat(hi[1])*X + rat(hi[2])
        Fz = sp.integrate(DENS, Z)
        g = sp.expand(Fz.subs(Z, zh) - Fz.subs(Z, zl))
        Fx = sp.integrate(g, X)
        h = sp.expand(Fx.subs(X, rat(xb[0]) + rat(xb[1])*K) - Fx.subs(X, rat(xa[0]) + rat(xa[1])*K))
        Fk = sp.integrate(h, K)
        total += Fk.subs(K, rat(kb)) - Fk.subs(K, rat(ka))
    return Fr(int(total.p), int(total.q))


T1, T2, T3 = sp.symbols('t1 t2 t3')


def _tetra(v0, v1, v2, v3):
    e = [[v[i] - v0[i] for i in range(3)] for v in (v1, v2, v3)]
    det = (e[0][0]*(e[1][1]*e[2][2] - e[1][2]*e[2][1]) - e[0][1]*(e[1][0]*e[2][2] - e[1][2]*e[2][0])
           + e[0][2]*(e[1][0]*e[2][1] - e[1][1]*e[2][0]))
    if det == 0:
        return Fr(0)
    sub = {K: rat(v0[0]) + rat(e[0][0])*T1 + rat(e[1][0])*T2 + rat(e[2][0])*T3,
           X: rat(v0[1]) + rat(e[0][1])*T1 + rat(e[1][1])*T2 + rat(e[2][1])*T3,
           Z: rat(v0[2]) + rat(e[0][2])*T1 + rat(e[1][2])*T2 + rat(e[2][2])*T3}
    poly = sp.Poly(sp.expand(DENS.subs(sub, simultaneous=True)), T1, T2, T3)
    tot = Fr(0)
    for (a, b, c), coef in poly.terms():
        tot += Fr(int(coef.p), int(coef.q)) * Fr(factorial(a)*factorial(b)*factorial(c), factorial(a + b + c + 3))
    return tot * abs(det)


def _cyclic(face, normal):
    """Order the vertices of a convex face by exact half-plane comparisons."""
    import functools
    c = tuple(sum(p[i] for p in face) / len(face) for i in range(3))
    def cross(u, v):
        return (u[1]*v[2] - u[2]*v[1], u[2]*v[0] - u[0]*v[2], u[0]*v[1] - u[1]*v[0])
    def dot(u, v):
        return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]
    ref = tuple(face[0][i] - c[i] for i in range(3))
    def half(p):
        d = tuple(p[i] - c[i] for i in range(3))
        s = dot(cross(ref, d), normal)
        if s > 0 or (s == 0 and dot(ref, d) > 0):
            return 0
        return 1
    def cmp(p, q):
        hp, hq = half(p), half(q)
        if hp != hq:
            return hp - hq
        dp = tuple(p[i] - c[i] for i in range(3)); dq = tuple(q[i] - c[i] for i in range(3))
        s = dot(cross(dp, dq), normal)
        return -1 if s > 0 else (1 if s < 0 else 0)
    return sorted(face, key=functools.cmp_to_key(cmp))


def mass_by_triangulation(P):
    vs = vertices(P)
    if len(vs) < 4:
        return Fr(0)
    ctr = tuple(sum(v[i] for v in vs) / len(vs) for i in range(3))
    if not all(val(c, ctr) > 0 for c in P):
        return Fr(0)        # the vertex centroid of a full-dimensional polytope is interior
    tot, seen = Fr(0), set()
    for c in P:
        face = [v for v in vs if val(c, v) == 0]
        if len(face) < 3 or frozenset(face) in seen:
            continue
        seen.add(frozenset(face))
        poly = _cyclic(face, c[:3])
        for i in range(1, len(poly) - 1):
            tot += _tetra(ctr, poly[0], poly[i], poly[i + 1])
    return tot


def mass(P):
    a, b = mass_by_slicing(P), mass_by_triangulation(P)
    check(a == b, f'the two integrations disagree: {a} != {b}')
    return a


def minus(pieces, B):
    """Pieces minus the convex set B, as disjoint convex pieces."""
    out = []
    for A in pieces:
        prefix = []
        for b in B:
            out.append(A + prefix + [(-b[0], -b[1], -b[2], -b[3])])
            prefix = prefix + [b]
    return out


# Chamber and regions in (k, x, z), k = x + y; Jacobian one.
OMEGA = [cons(0, 1, 0, 0), cons(1, -2, 0, 0), cons(-1, 1, 1, 0), cons(0, 0, -1, 1)]
N0 = OMEGA + [cons(1, 0, 1, -1), cons(-1, 0, -1, Fr(3, 2)), cons(1, 0, 0, -HALF), cons(0, 1, -1, HALF)]
RBAL = [cons(1, 0, 1, -1), cons(-1, 0, -1, Fr(15, 14)), cons(-28, 0, -7, 18)]   # 1<r<15/14, 21k+7r<18


def kappa(s):
    return 1 / (2 - s)


def kband(k0, k1):
    return [cons(1, 0, 0, -k0), cons(-1, 0, 0, k1)]


def mark_cap(s0, s1, a, b):
    """s0 <= s < s1 and beta < a + b*s, written in (k, x): x < k*a + b*(2k-1)."""
    return kband(kappa(s0), kappa(s1)) + [cons(a + 2*b, -1, 0, -b)]


# Mark ranges of the extended four-shift row (prop:fourshiftplus, lem:cases).
ALL_MARKS = kband(HALF, Fr(10, 19))                                         # 0 < s < 1/10
TWO_MARKS = mark_cap(Fr(1, 10), Fr(1, 8), Fr(3, 2), Fr(-21, 2))            # beta < (3-21s)/2
LEVEL = [mark_cap(Fr(1, 10), Fr(1, 7), Fr(1, 2), Fr(-7, 4)),                # beta < (2-7s)/4
         mark_cap(Fr(1, 7), Fr(1, 4), Fr(1, 4), Fr(-1, 2)),                 # beta < (1-2s)/4
         mark_cap(Fr(1, 4), Fr(1, 3), Fr(1, 2), Fr(-3, 2))]                 # beta < (1-3s)/2


def cell(k0, k1, xlo, xhi, zlo):
    """k0<k<k1, xlo(k)<x<xhi(k), zlo<z<1/2+x; xlo, xhi = (a, b) for a + b*k."""
    P = [cons(1, 0, 0, -k0), cons(-1, 0, 0, k1), cons(-xlo[1], 1, 0, -xlo[0]),
         cons(xhi[1], -1, 0, xhi[0]), cons(0, 1, -1, HALF)]
    P.append(cons(1, 0, 1, -1) if zlo == '1-k' else cons(-1, 1, 1, 0))
    return P


START, TURN = (Fr(-1, 4), Fr(1, 2)), (Fr(-1), Fr(2))           # (k-1/2)/2, 2k-1
HALFK = (Fr(0), Fr(1, 2))
A0, A1, A2, A3 = (Fr(21, 2), Fr(-39, 2)), (Fr(7, 4), Fr(-3)), (Fr(1, 2), Fr(-3, 4)), (Fr(3, 2), Fr(-5, 2))

STAGES = [
    # (name, cells with the mark range that covers each, convex pieces of the new range, previous ranges)
    ('all marks, 1/2<kappa<10/19', [], [ALL_MARKS], []),
    ('two marks, 10/19<kappa<8/15',
     [(cell(Fr(10, 19), Fr(8, 15), START, TURN, 'k-x'), TWO_MARKS),
      (cell(Fr(10, 19), Fr(8, 15), TURN, A0, '1-k'), TWO_MARKS)],
     [TWO_MARKS], [ALL_MARKS]),
    ('represented levels, kappa<3/5',
     [(cell(Fr(35, 66), Fr(8, 15), A0, A1, '1-k'), LEVEL[0]),
      (cell(Fr(8, 15), Fr(7, 13), START, TURN, 'k-x'), LEVEL[0]),
      (cell(Fr(8, 15), Fr(7, 13), TURN, A1, '1-k'), LEVEL[0]),
      (cell(Fr(7, 13), Fr(6, 11), START, TURN, 'k-x'), LEVEL[1]),
      (cell(Fr(7, 13), Fr(6, 11), TURN, A2, '1-k'), LEVEL[1]),
      (cell(Fr(6, 11), Fr(4, 7), START, A2, 'k-x'), LEVEL[1]),
      (cell(Fr(4, 7), Fr(7, 12), START, A3, 'k-x'), LEVEL[2])],
     LEVEL, [ALL_MARKS, TWO_MARKS]),
]
STAGE1 = Fr(1719450085703065, 41304025315712)
STAGE2 = Fr(22036996747165861198040059, 529288496282004750000000)
SEVEN = Fr(268755110285287452500182503673016801, 49130135420790450741077959596000000000)


def section1():
    print('Section 1: support mass')
    check(mass(OMEGA) == 42, 'mu(Omega) = 42')
    muN0, muN0R = mass(N0), mass(N0 + RBAL)
    check(muN0 == Fr(209, 1024), 'mu(N0)')
    check(muN0R == Fr(62748701, 30991570176), 'mu(N0 cap R)')
    check(42 - 2*(muN0 - muN0R) == C0, 'C0')
    print('  mu(N0) = 209/1024, mu(N0 cap R) = 62748701/30991570176, C0 =', C0)
    coeff = C0
    for name, cells, new, old in STAGES:
        # the newly covered set, from the mark ranges alone
        region = Fr(0)
        for piece in new:
            pcs = [N0 + piece]
            for prev in old + [RBAL]:
                pcs = minus(pcs, prev)
            region += sum((mass(p) for p in pcs), Fr(0))
        gain = 2*region
        if cells:
            tot = Fr(0)
            for idx, (P, rng) in enumerate(cells):
                vs = vertices(P)
                check(len(vs) >= 4, f'{name}: cell {idx} is degenerate')
                for c in N0 + rng:
                    check(all(val(c, v) >= 0 for v in vs), f'{name}: cell {idx} leaves N0 or its mark range')
                for prev in old + [RBAL]:
                    check(mass(P + prev) == 0, f'{name}: cell {idx} meets an earlier region')
                tot += 2*mass(P)
            for (P, _), (Q, _) in combinations(cells, 2):
                check(mass(P + Q) == 0, f'{name}: two cells overlap')
            check(tot == gain, f'{name}: the cells do not exhaust the new region')
        coeff += gain
        print(f'  {name}: gain {gain} = {float(gain):.18f}; coefficient {float(coeff):.15f}')
        if name.startswith('all marks'):
            check(coeff == STAGE1, 'stage-1 coefficient')
        if name.startswith('two marks'):
            check(coeff == STAGE2, 'stage-2 coefficient')
        if name.startswith('represented'):
            check(gain == SEVEN, 'seven-cell gain')
    check(coeff == FINAL, 'final coefficient')
    # the mark range continues past 7/12 without adding projected mass
    tail = [N0 + kband(Fr(7, 12), kappa(Fr(1, 3))) + LEVEL[2]]
    check(sum((mass(p) for p in tail), Fr(0)) == 0, 'no projected mass for 7/12<kappa<3/5')
    return coeff


# ---------------------------------------------------------------- Section 2
VNAMES = ['s', 'gamma', 'eta', 'v', 'i', 'z', 'x', 'E', 'm', 'n', 'w', 'gap']


def lf(**kw):
    """Linear form as a dict; key '1' is the constant."""
    return {k: Fr(v) for k, v in kw.items() if Fr(v) != 0}


def add(*forms, coeffs=None):
    out = {}
    coeffs = coeffs or [1]*len(forms)
    for f, c in zip(forms, coeffs):
        for k, v in f.items():
            out[k] = out.get(k, Fr(0)) + Fr(c)*v
    return {k: v for k, v in out.items() if v != 0}


def var(name):
    return {name: Fr(1)}


ONE = {'1': Fr(1)}


def sc(c, f):
    return {k: Fr(c)*v for k, v in f.items() if Fr(c)*v != 0}


def branch_systems(fixed_level):
    """Rebuild every branch: a list (label, rows) of linear forms required >= 0."""
    s, g, eta, v, i, z, x, E, m, n, w, gap = (var(nm) for nm in VNAMES)
    sigma = add(ONE, g, eta, coeffs=[1, -1, -1])
    tau = add(s, g, eta, v, coeffs=[1, -2, -3, Fr(-9, 10)])
    D = add(ONE, s, g, eta, v, i, coeffs=[1, 1, -3, -4, -1, 1])
    j = add(D, m, n, coeffs=[1, -1, -1])
    a, b = add(sigma, n, coeffs=[1, -1]), add(sigma, m, coeffs=[1, -1])
    Zs, y = add(z, x), add(j, x, coeffs=[1, -1])
    C = add(sigma, Zs, coeffs=[1, -1])
    u = add(j, v, i, Zs, E, coeffs=[1, Fr(1, 10), -1, -1, -1])
    Bstar = add(sigma, tau, coeffs=[HALF, 2])
    budget = add(sigma, y, tau, coeffs=[2, 1, -1])
    common = [ONE] + [var(nm) for nm in VNAMES] + [
        tau, add(g, eta, i, coeffs=[3, 4, -1]), add(m, n, coeffs=[1, -1]), add(n, j, coeffs=[2, -1]), y,
        add(Zs, E, coeffs=[1, -1]), add(a, E, coeffs=[1, -1]), add(C, w, coeffs=[1, -1]),
        add(ONE, w, coeffs=[HALF, -1]), add(sigma, tau, m, coeffs=[HALF, 1, -1]), u]
    pair_split = [add(tau, j, coeffs=[2, -1]), add(Bstar, m, n, coeffs=[1, -1, -1])]
    Dm = add(D, m, coeffs=[1, -1])
    single_split = [add(tau, m, coeffs=[2, -1]), add(tau, Dm, coeffs=[2, -1]), add(Bstar, Dm, coeffs=[1, -1])]
    completion = [add(u, C, coeffs=[1, -HALF]), add(u, C, b, coeffs=[1, HALF, -1])]
    c, d = add(C, w, coeffs=[1, -1]), add(a, E, coeffs=[1, -1])
    R = add(b, eta, z, i, E)
    N = add(eta, y, coeffs=[2, 1])
    Kset = [add(c, w, p, q) for p in (add(R, w), N) for q in (c, add(R, d))] \
         + [add(c, d, w, p, R, coeffs=[2, 1, 1, HALF, HALF]) for p in (add(R, w), N)] \
         + [add(d, N, R, coeffs=[2, 1, 1])]
    direct = [add(y, b, w, z, kk, budget, coeffs=[1, 1, 1, -1, 1, -2]) for kk in Kset]
    extras = [None]
    if fixed_level:
        J = add(C, d, coeffs=[1, -1])
        level = add(R, w)
        exceptional = add(C, J, N, R, w, coeffs=[1, 1, 1, Fr(-3, 2), -2])
        common = common + [J]
        base = add(d, R, b, w, J, y, budget, coeffs=[2, 1, 2, 2, 1, 1, -2])
        extras = [add(base, l1, l2, l3) for l1, l2, l3 in product(
            ({}, add(J, level, coeffs=[1, -1])), ({}, add(N, level, coeffs=[1, -1])),
            ({}, sc(Fr(7, 16), exceptional)))]
        bands = [(Fr(1, 10), Fr(1, 7), (Fr(1, 2), Fr(-7, 4))), (Fr(1, 7), Fr(1, 4), (Fr(1, 4), Fr(-1, 2))),
                 (Fr(1, 4), Fr(1, 3), (Fr(1, 2), Fr(-3, 2)))]
    else:
        bands = [(Fr(1, 10), Fr(1, 7), (Fr(13, 30), Fr(-47, 30))), (Fr(1, 7), Fr(1, 4), (Fr(7, 30), Fr(-19, 30)))]
    out = []
    for s0, s1, (ca, cb) in bands:
        dom = common + [add(s, ONE, coeffs=[1, -s0]), add(ONE, s, gap, coeffs=[s1, -1, -1]),
                        add(ONE, s, w, gap, coeffs=[ca, cb, -1, -1])]
        primal = [(p, q) for p in pair_split for q in single_split]
        if s0 >= Fr(1, 4):
            primal.append((add(tau, sigma, coeffs=[4, -1]),))
        rows_band = []
        for ci, ch in enumerate(primal):
            for ri, r3 in enumerate(completion):
                for ki, r4 in enumerate(direct):
                    for ei, ex in enumerate(extras):
                        rows = dom + list(ch) + [r3, r4]
                        if fixed_level:
                            rows = rows + [add(r4, E, z, coeffs=[1, -1, 1]), ex]
                        rows_band.append((f'{ci}.{ri}.{ki}.{ei}', rows))
        out.append((f"{'level' if fixed_level else 'completion'} {s0}<=s<{s1}", rows_band))
    return out


def at_family(f):
    """Evaluate a linear form on the equality family of the completion bands."""
    s = sp.symbols('s')
    vals = {'s': s, 'gamma': 0, 'v': 0, 'x': 0, 'eta': (7*s - 1)/24, 'i': (7*s - 1)/6,
            'm': (1 + s)/4, 'n': (1 + s)/4, 'z': (19 - 13*s)/120, 'E': (19 - 13*s)/120,
            'w': (7 - 19*s)/30, 'gap': 0, '1': 1}
    return sp.expand(sum(sp.Rational(c.numerator, c.denominator)*vals[k] for k, c in f.items()))


def section2():
    print('Section 2: case analysis')
    with open(os.path.join(HERE, 'mixed_row_certificates.json')) as fh:
        certs = json.load(fh)
    expected = {'completion 1/10<=s<1/7': 84, 'completion 1/7<=s<1/4': 84,
                'level 1/10<=s<1/7': 672, 'level 1/7<=s<1/4': 672, 'level 1/4<=s<1/3': 784}
    seen = {}
    for fixed in (False, True):
        for band, branches in branch_systems(fixed):
            check(band in certs, f'no certificates for {band}')
            check(len(branches) == expected[band], f'{band}: {len(branches)} branches')
            for label, rows in branches:
                cert = certs[band].get(label)
                check(cert is not None, f'{band} {label}: missing certificate')
                target = {'gap': Fr(-1)} if cert['target'] == '-gap' else {'1': Fr(-1)}
                comb = {}
                for idx, q in cert['multipliers']:
                    lam = Fr(q)
                    check(lam >= 0, f'{band} {label}: negative multiplier')
                    check(0 <= idx < len(rows), f'{band} {label}: bad row index')
                    for k, vv in rows[idx].items():
                        comb[k] = comb.get(k, Fr(0)) + lam*vv
                comb = {k: vv for k, vv in comb.items() if vv != 0}
                check(comb == target, f'{band} {label}: certificate does not combine to {cert["target"]}')
            seen[band] = len(branches)
            print(f'  {band}: {len(branches)} branches certified')
    check(seen == expected, 'branch counts 84/84/672/672/784')
    # Sanity identity: on the equality family m = 2tau, u = b - C/2 and the second
    # direct entry vanishes (three thresholds meet on the second completion face).
    band, branches = branch_systems(False)[1]
    rows = dict(branches)['0.1.1.0']
    tail = rows[-4:]          # pair-split entry, single-split entry, completion entry, direct entry
    check(at_family(tail[1]) == 0 and at_family(tail[2]) == 0 and at_family(tail[3]) == 0,
          'equality family of the completion bands')
    return True


def section3(coeff):
    print('Section 3: variance')
    var_ = (coeff - 2) / 2
    check(var_ == Fr(107255439608257758165130001068964060975875789, 5411392952492500296371592945251676479926272),
          'variance lower limit')
    check(Fr(198203014547032, 10**13) < var_ < Fr(198203014547033, 10**13), 'variance decimal')
    check(Fr(416406029094064, 10**13) < coeff < Fr(416406029094065, 10**13), 'coefficient decimal')
    print(f'  (C-2)/2 = {var_} = {float(var_):.13f}')


# ---------------------------------------------------------------- Section 4
# The ceiling of prop:ceiling with the mixed-row region F+ in its list.
CEIL_OLD = Fr(493586674117277079727, 11767111801200000000)
CEIL_INC = Fr(196813181035147418047099, 474637777079666241191850000000)
CEIL_NEW = Fr(13860404849860091, 330432202525696)


def section4():
    print('Section 4: ceiling')
    band = [cons(1, 0, 1, -1), cons(-1, 0, -1, 2)]                          # 1 < r < 2
    bset = [cons(0, 1, 0, -Fr(1, 4)), cons(0, 0, -1, Fr(3, 4)),           # x > 1/4, z < 3/4
            cons(1, 0, -1, 0), cons(-1, 2, -1, 1)]                          # x+y > z, y+z-x < 1
    muB = mass(OMEGA + band + bset)
    check(muB == Fr(55, 1024), 'mu(B)')
    muBR = 2*mass(OMEGA + band + bset + RBAL)
    check(muBR == Fr(134173355669, 1470888975150000000), '2 mu(B cap R)')
    check(42 - muB + muBR == CEIL_OLD, 'release ceiling')
    lower = [cons(1, 0, 1, -1), cons(-1, 0, -1, Fr(3, 2))]                 # 1 < r < 3/2
    inc, prev = Fr(0), []
    for piece in [ALL_MARKS, TWO_MARKS] + LEVEL:
        pcs = [OMEGA + lower + bset + piece]
        for p in prev + [RBAL]:
            pcs = minus(pcs, p)
        inc += sum((mass(p) for p in pcs), Fr(0))
        prev.append(piece)
    inc *= 2
    check(inc == CEIL_INC, 'ceiling increment from F+')
    check(CEIL_OLD + inc == CEIL_NEW, 'new ceiling')
    check(Fr(419462895683, 10**10) < CEIL_NEW < Fr(419462895684, 10**10), 'ceiling decimal')
    print(f'  release ceiling {float(CEIL_OLD):.15f}; with F+ {float(CEIL_NEW):.15f}')


# ---------------------------------------------------------------- Section 5
# The prose case analyses of lem:cases (i) (0 < s < 1/10, every mark) and (ii)
# (1/10 <= s < 1/8, beta < (3-21s)/2), transcribed with four individual primal degrees
# d1 >= d2 >= d3 >= d4, all seven bilinear splits, the powerful-part degree p free where
# the source allows it, and every degree in [0, 10] (all are in fact at most 2).  A leaf
# is: hypotheses + one failure alternative of the spectral estimates + one option for each
# split.  The stored certificates sit at nodes of this disjunction tree; a certificate at
# a node uses only constraints present at every leaf below it.  We check each certificate
# exactly and that the certified nodes cover every leaf.
S5 = sp.symbols('s g eta p v i z x E w gap d1 d2 d3 d4 D')
S5_NAMES = [str(t) for t in S5]


def _s5_form(expr):
    pe = sp.Poly(sp.expand(expr), *S5)
    out = {}
    for t, nm in zip(S5, S5_NAMES):
        c = sp.Rational(pe.coeff_monomial(t))
        if c != 0:
            out[nm] = Fr(int(c.p), int(c.q))
    c0 = sp.Rational(pe.coeff_monomial(1))
    if c0 != 0:
        out['1'] = Fr(int(c0.p), int(c0.q))
    return out


def stage12_systems():
    s, g, eta, p, v, i, z, x, E, w, gap, d1, d2, d3, d4, D = S5
    R_ = sp.Rational
    sigma = 1 - g - eta
    lam = 1 + s - 3*g - 4*eta - v
    tauP = s - 2*g - 3*eta - p/2 - R_(9, 10)*v
    tau0 = s - 2*g - 3*eta - R_(9, 10)*v
    m, n, j = d1, d2, d3 + d4
    hyp = [d1 - d2, d2 - d3, d3 - d4, D - (d1 + d2 + d3 + d4), (d1 + d2 + d3 + d4) - D,
           D - lam, 1 + s - D, 3*g + 4*eta - i, tauP, sigma, (sigma + p)/2 + tauP - m]
    L0 = (sigma + p)/2 + 2*tauP
    degs = [d1, d2, d3, d4]
    splits = []
    for r in (1, 2):
        for S in combinations(range(4), r):
            if r == 2 and 0 not in S:
                continue
            a = sum(degs[k] for k in S)
            bb = sum(degs[k] for k in range(4) if k not in S)
            splits.append([[2*tauP - a], [2*tauP - bb], [L0 - a, L0 - bb]])
    a, b = sigma - n, sigma - m
    # (i): x = 0 by monotonicity; square margins of lem:square at x = E = 0
    f = z + i
    h1 = hyp + [R_(1, 10) - s - gap, x, -x]
    fails1 = [[-(m - n/2 - j - i - R_(1, 5)*v + z/2), f + 2*b + a - (sigma - z)],
              [-(a - j - f/2 - R_(1, 5)*v + 2*z), (sigma - z) - f - 2*b - a],
              [-(a/2 - j - f/2 - R_(1, 5)*v + 2*z)],
              [-((sigma - z) - b/2 - R_(3, 2)*j - (eta + f)/2 - R_(1, 5)*v + 2*z)],
              [-(b - j - R_(1, 5)*v + 2*z)],
              [-(b - j - eta - R_(1, 5)*v)]]
    # (ii): square margins P1-P3 and the direct estimate with the pooled l
    Z, y = z + x, j - x
    Cc = sigma - Z
    h2 = hyp + [s - R_(1, 10), R_(1, 8) - s - gap, (3 - 21*s)/2 - w - gap, Cc - w, R_(1, 2) - w,
                y, Z - E, a - E, tau0]
    P1 = m - n/2 - j - i - R_(1, 5)*v + (Z + E)/2
    P2 = a/2 - j - i/2 - R_(1, 5)*v + R_(3, 2)*z + x + E
    P3 = (sigma + m)/2 - R_(3, 2)*j - (eta + i)/2 - R_(1, 5)*v + z/2 + x/2 + R_(3, 2)*E
    ordR = (i + z + E + 2*b) + (a - E) - Cc
    sq = [[-P1, ordR], [-(P2 + (a - E)/2), -ordR], [-P2], [-P3], [-(b - j - 2*eta - R_(1, 5)*v)]]
    B = 2*sigma + y - tau0
    c, d = Cc - w, a - E
    R, N = b + eta + z + i + E, 2*eta + y
    K = [c + w + pp + qq for pp in (R + w, N) for qq in (c, R + d)] \
        + [2*c + d + w + (pp + R)/2 for pp in (R + w, N)] + [2*d + N + R]
    direct = [[y + b + w - z + kk - 2*B] for kk in K]
    fails2 = [u + t for u in sq for t in direct]
    conv = lambda L: [[_s5_form(e) for e in opt] for opt in L]
    return {'stage 1': ([_s5_form(e) for e in h1], [conv(fails1)] + [conv(sp_) for sp_ in splits]),
            'stage 2': ([_s5_form(e) for e in h2], [conv(fails2)] + [conv(sp_) for sp_ in splits])}


S5_BOUNDS = [{nm: Fr(1)} for nm in S5_NAMES] + [{nm: Fr(-1), '1': Fr(10)} for nm in S5_NAMES] + [{'1': Fr(1)}]


def s5_rows(hyp, levels, path):
    rows = list(hyp)
    for lv, choice in enumerate(path):
        rows += levels[lv][choice]
    return rows + S5_BOUNDS


def section5():
    print('Section 5: prose case analyses (i) and (ii)')
    with open(os.path.join(HERE, 'mixed_row_certificates.json')) as fh:
        certs = json.load(fh)
    for name, (hyp, levels) in stage12_systems().items():
        stored = certs.get('tree ' + name)
        check(stored is not None, f'no certificates for {name}')
        paths = set()
        for path, tname, mult in stored:
            path = tuple(path)
            check(len(path) <= len(levels) and all(0 <= c < len(levels[k]) for k, c in enumerate(path)),
                  f'{name}: bad node {path}')
            rows = s5_rows(hyp, levels, path)
            target = {'gap': Fr(-1)} if tname == '-gap' else {'1': Fr(-1)}
            comb = {}
            for idx, q in mult:
                lam = Fr(q)
                check(lam >= 0 and 0 <= idx < len(rows), f'{name} {path}: bad multiplier')
                for k, vv in rows[idx].items():
                    comb[k] = comb.get(k, Fr(0)) + lam*vv
            check({k: vv for k, vv in comb.items() if vv != 0} == target,
                  f'{name} {path}: certificate does not combine to {tname}')
            paths.add(path)

        def covered(prefix):
            if prefix in paths:
                return True
            if len(prefix) == len(levels):
                return False
            return all(covered(prefix + (c,)) for c in range(len(levels[len(prefix)])))
        check(covered(()), f'{name}: some branch has no certificate')
        leaves = 1
        for L in levels:
            leaves *= len(L)
        print(f'  {name}: all {leaves} branches covered by {len(paths)} exact certificates')


# ---------------------------------------------------------------- Section 6
# The affine identities quoted in sec:mixedrow (lem:degrees through lem:cases), checked by
# expansion, and the coefficient of rem:fallback (no represented-level estimate).
FALLBACK = Fr(1767870158617164811674095218440187374694865783,
              42458728008803622772455544218525820350000000)


def section6():
    print('Section 6: affine identities and the fallback coefficient')
    s, g, eta, v, i, z, x, E, m, n, w = sp.symbols('s g eta v i z x E m n w')
    R_ = sp.Rational
    sigma = 1 - g - eta
    lam = 1 + s - 3*g - 4*eta - v
    tau = s - 2*g - 3*eta - R_(9, 10)*v
    D = lam + i
    j = D - m - n
    a, b = sigma - n, sigma - m
    Z, y = z + x, D - m - n - x
    C = sigma - Z
    u = j + v/10 - i - Z - E
    Bs = sigma/2 + 2*tau
    B = 2*sigma + y - tau
    c, d = C - w, a - E
    R, N = b + eta + z + i + E, 2*eta + y
    J = C - d
    X = C + R/2 - (J + N)/2
    count = [0]

    def ident(name, lhs, rhs):
        check(sp.expand(lhs - rhs) == 0, f'identity {name}')
        count[0] += 1

    # lem:labels, lem:degrees: [Y_1] = D + v; lem:unsignedplus
    ident('[Y]', i + 3*sigma - eta - (2 - s), D + v)
    ident('sigma-2tau', sigma - 2*tau, 1 - 2*s + 3*g + 5*eta + R_(9, 5)*v)
    ident('sigma-4tau', sigma - 4*tau, 1 - 4*s + 7*g + 11*eta + R_(18, 5)*v)
    # lem:doublepoisson and the normalisation
    ident('u', tau + sigma - m - n - Z - E, u)
    ident('trivial l', tau + sigma - m - n, j + v/10 - i)
    ident('budget B', (C + y + a - E + b) - u, B)
    # lem:square: allowable exponent and margins P0-P3
    Aw = sigma + z - x + a + 2*b - v/5 + E
    ident('allowable', C + (a - E) + 2*y + 2*b - 2*(j + v/10 - Z - E), Aw)
    Rp, K0 = z + i + E + 2*b, eta + y + b
    ident('P0', Aw - (C + (a - E) + y + b), b - j - v/5 + 2*z + x + 2*E)
    ident('P1', Aw - (y + b) - (C + 2*Rp + (a - E))/2, m - n/2 - j - i - v/5 + (Z + E)/2)
    ident('P2', Aw - (y + b) - (2*C + (a - E) + Rp)/2, a/2 - j - i/2 - v/5 + R_(3, 2)*z + x + E)
    ident('P3', Aw - (y + b) - (2*(a - E) + K0 + Rp)/2,
          (sigma + m)/2 - R_(3, 2)*j - (eta + i)/2 - v/5 + z/2 + x/2 + R_(3, 2)*E)
    # lem:direct: the seven margins 2M_k = 2B - (y + b + w - z + k)
    K = {('Rw', 'c'): c + w + (R + w) + c, ('Rw', 'Rd'): c + w + (R + w) + (R + d),
         ('N', 'c'): c + w + N + c, ('N', 'Rd'): c + w + N + (R + d),
         ('Rw',): 2*c + d + w + (R + w + R)/2, ('N',): 2*c + d + w + (N + R)/2, (): 2*d + N + R}
    M2 = {k: 2*B - (y + b + w - z + f) for k, f in K.items()}
    ident('M(Rw,c)', M2[('Rw', 'c')], 1 - s + g + eta + R_(4, 5)*v + (m - n) + (Z - E) + z - w)
    ident('M(N,c)', M2[('N', 'c')], 1 - 2*s + 3*g + 3*eta + R_(9, 5)*v + m + 2*x + 3*z)
    ident('M(N,Rd)', M2[('N', 'Rd')], 2*m + n - 2*s + 4*g + 3*eta - i + R_(9, 5)*v + x + z - w)
    ident("M'(N)", M2[('N',)], m + n/2 - R_(3, 2)*s + 3*g + 3*eta + R_(13, 10)*v + R_(3, 2)*x + R_(5, 2)*z + E/2)
    ident('M1', M2[('Rw', 'Rd')]/2, m - s/2 + g + eta/2 + R_(2, 5)*v - w - i/2 - E/2)
    ident('M2', M2[('Rw',)], m - s + 2*g + 2*eta + R_(4, 5)*v - w/2 + Z + z)
    ident('M3', M2[()], 2*(m + n) - 2*tau - 3*eta - i + E - w)
    # lem:actuallevel
    ident('J', J, n - Z + E)
    ident('2X', 2*X, 2 - s + v)
    ident('exceptional', X - (2*(R + w) - R_(3, 2)*(J + N)), C + J + N - R_(3, 2)*R - 2*w)
    ident('C - J = d', C - J, d)
    # lem:cases, preliminaries
    ident('2lam/3-B*', 2*lam/3 - Bs, R_(1, 6) - R_(4, 3)*s + R_(5, 2)*g + R_(23, 6)*eta + R_(17, 15)*v)
    ident('lam-B*-4tau', lam - Bs - 4*tau, R_(1, 2) - 5*s + R_(19, 2)*g + R_(29, 2)*eta + R_(22, 5)*v)
    ident('lam-4tau', lam - 4*tau, 1 - 3*s + 5*g + 8*eta + R_(13, 5)*v)
    ident('sigma-B*-2tau', sigma - Bs - 2*tau, sigma/2 - 4*tau)
    ident('C lower', sigma - (1 + s)/2 - v/10, R_(1, 2) - s/2 - g - eta - v/10)
    # Step 2 (j <= 2 tau)
    I_ = 3*g + 4*eta
    ident('Step2 b-j', sigma/2 - 3*tau - 2*eta - v/5, R_(1, 2) - 3*s + R_(11, 2)*g + R_(13, 2)*eta + R_(5, 2)*v)
    ident('Step2 4P1', lam - 10*tau - 4*I_ - R_(4, 5)*v, 1 - 9*s + 5*g + 10*eta + R_(36, 5)*v)
    ident('Step2 4P2', 2*sigma - (1 + s) - 6*tau - 2*I_ - R_(4, 5)*v, 1 - 7*s + 4*g + 8*eta + R_(23, 5)*v)
    ident('Step2 P3', sigma/2 - 3*tau - (eta + I_)/2 - v/5, R_(1, 2) - 3*s + 4*g + 6*eta + R_(5, 2)*v)
    # (ii) case 1
    ident('case1 M1a', (lam - 2*tau)/2 - s/2 + g + eta/2 + R_(2, 5)*v - I_/2,
          R_(1, 2) - s - eta/2 + R_(4, 5)*v)
    Efail = (9*s - 1 - 5*g - 10*eta - R_(36, 5)*v)/2
    ident('case1 M1b', R_(1, 2) - s - eta/2 + R_(4, 5)*v - Efail/2,
          R_(3, 4) - R_(13, 4)*s + R_(5, 4)*g + 2*eta + R_(13, 5)*v)
    ident('case1 cap', R_(3, 4) - R_(13, 4)*s - (3 - 21*s)/2, (29*s - 3)/4)
    ident('case1 M2', (lam - 2*tau)/2 - s, R_(1, 2) - R_(3, 2)*s + g/2 + eta + R_(2, 5)*v)
    ident('case1 M3', 2*(lam - 2*tau) - 2*tau - 3*eta - I_, 2 - 4*s + 3*g + 3*eta + R_(17, 5)*v)
    # (ii) case 2
    ident('case2 b-j', sigma/2 - 4*tau - 2*eta - v/5, R_(1, 2) - 4*s + R_(15, 2)*g + R_(19, 2)*eta + R_(17, 5)*v)
    ident('case2 P1', (lam - 6*tau) - tau - 4*tau - I_ - v/5, 1 - 10*s + 16*g + 25*eta + R_(87, 10)*v)
    ident('case2 P2', (sigma - 2*tau)/2 - 4*tau - I_/2 - v/5, R_(1, 2) - 5*s + 8*g + R_(25, 2)*eta + R_(43, 10)*v)
    ident('case2 P3', (sigma + lam - 6*tau)/2 - R_(3, 2)*4*tau - (eta + I_)/2 - v/5,
          1 - R_(17, 2)*s + R_(29, 2)*g + 22*eta + R_(37, 5)*v)
    ident('case2 M1', (lam - 6*tau) - s/2 + g + eta/2 + R_(2, 5)*v - I_/2,
          1 - R_(11, 2)*s + R_(17, 2)*g + R_(25, 2)*eta + R_(24, 5)*v)
    ident('case2 cap', 1 - R_(11, 2)*s - (3 - 21*s)/2, 5*s - R_(1, 2))
    ident('case2 M2', (lam - 6*tau) - s, 1 - 6*s + 9*g + 14*eta + R_(22, 5)*v)
    ident('case2 M3', 2*lam - 10*tau - 3*eta, 2 - 8*s + 14*g + 19*eta + 7*v)
    # the slope of F_* in the degree of the b-dyad
    check(Fr(3, 2) - Fr(1, 2) - Fr(1, 2) - Fr(3, 2)*Fr(7, 32) == Fr(11, 64), 'slope of F_*')
    print(f'  {count[0]} affine identities verified')
    # rem:fallback: the mark ranges without lem:actuallevel
    completion = [mark_cap(Fr(1, 10), Fr(1, 7), Fr(13, 30), Fr(-47, 30)),
                  mark_cap(Fr(1, 7), Fr(1, 4), Fr(7, 30), Fr(-19, 30))]
    gain, prev = Fr(0), []
    for piece in [ALL_MARKS, TWO_MARKS] + completion:
        pcs = [N0 + piece]
        for p in prev + [RBAL]:
            pcs = minus(pcs, p)
        gain += sum((mass(p) for p in pcs), Fr(0))
        prev.append(piece)
    coeff = C0 + 2*gain
    check(coeff == FALLBACK, 'fallback coefficient')
    check(Fr(416373792038, 10**10) < coeff < Fr(416373792039, 10**10), 'fallback decimal')
    print(f'  fallback coefficient {coeff} = {float(coeff):.13f}')


if __name__ == '__main__':
    coeff = section1()
    section2()
    section3(coeff)
    section4()
    section5()
    section6()
    print('ALL CHECKS PASSED: C =', coeff, '=', f'{float(coeff):.15f}')
    sys.exit(0)
