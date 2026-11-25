"""Checks for the factorable-moduli section of the zeta paper (paper/main.tex).

1. The mass of the new region, by exact polynomial integration (SymPy),
   independently of the Newton--Cotes rule in factorable_polygon_check.py.
2. The exponent identities used in the covering argument.
3. A random test of the covering argument: at every sampled parameter point
   one of the three estimates (bilinear, one smooth variable, two smooth
   variables) saves more than the required power.
4. Local facts about the kernel K_d: the prime formula, the bound 9 at prime
   powers, the Chinese remainder factorisation, the Fourier transform at
   primes, and the size of the two- and four-factor correlation sums.

Run with:  python3 -B computations/factorable_row_checks.py
"""

import cmath
import math
import random
from fractions import Fraction as Fr

import sympy as sp

# ---------------------------------------------------------------------------
# 1. Mass of the new region
# ---------------------------------------------------------------------------


def mass_increment():
    k, x, z = sp.symbols("k x z")
    dens = sp.Rational(math.factorial(9), 2) * (k - 2 * x) ** 2 * (z - x) ** 2 * (z - k + x) ** 2
    z0 = (18 - 28 * k) / sp.Integer(7)
    inner = sp.integrate(dens, (z, z0, sp.Rational(1, 2) + x))
    xtop = k / 2 - sp.Rational(3, 2) * (2 * k - 1)
    lo1 = z0 - sp.Rational(1, 2)          # 1/2 < k < 99/196
    lo2 = 5 * (2 * k - 1)                 # 99/196 < k < 13/25
    kc, ke = sp.Rational(99, 196), sp.Rational(13, 25)
    assert sp.simplify(lo1.subs(k, kc) - lo2.subs(k, kc)) == 0
    assert sp.simplify(lo2.subs(k, ke) - xtop.subs(k, ke)) == 0
    part1 = sp.integrate(sp.integrate(inner, (x, lo1, xtop)), (k, sp.Rational(1, 2), kc))
    part2 = sp.integrate(sp.integrate(inner, (x, lo2, xtop)), (k, kc, ke))
    inc = sp.nsimplify(part1 + part2)
    C0 = sp.Rational(2578241177999, 61983140352)
    assert inc == sp.Rational(840731426179152778718787, 52986177566328125000000000), inc
    C = C0 + inc
    assert C == sp.Rational(3307268442615739142376085993, 79479266349492187500000000)
    # Region facts used in the text (vertices suffice: all faces are affine).
    for (ka, kb, lo) in ((sp.Rational(1, 2), kc, lo1), (kc, ke, lo2)):
        for kk in (ka, kb):
            for xx in (lo.subs(k, kk), xtop.subs(k, kk)):
                for zz in (z0.subs(k, kk), sp.Rational(1, 2) + xx):
                    assert 0 <= xx <= kk - xx <= zz <= 1
                    assert 1 <= kk + zz <= sp.Rational(3, 2)
                    assert zz - xx <= sp.Rational(1, 2)
                    assert 21 * kk + 7 * (kk + zz) >= 18
    return inc, C


# ---------------------------------------------------------------------------
# 2. Exponent identities
# ---------------------------------------------------------------------------


def exponent_identities():
    s, b, p, g, e, v = sp.symbols("s b p gamma eta v")
    lam = 1 + s - 3 * g - 4 * e - v
    tau = s - 2 * g - 3 * e - p / 2 - sp.Rational(9, 10) * v
    hs, ks = b + p, (1 - b) / 2
    checks = {
        "lam-4tau-2h": (lam - 4 * tau - 2 * hs, 1 - 3 * s - 2 * b + 5 * g + 8 * e + sp.Rational(13, 5) * v),
        "lam-6tau-2k": (lam - 6 * tau - 2 * ks, b - 5 * s + 9 * g + 14 * e + 3 * p + sp.Rational(22, 5) * v),
        "lam-8tau": (lam - 8 * tau, 1 - 7 * s + 13 * g + 20 * e + 4 * p + sp.Rational(31, 5) * v),
        "single": (lam - 3 * tau - (1 + b + p - g - e) / 2,
                   (1 - b) / 2 - 2 * s + sp.Rational(7, 2) * g + sp.Rational(11, 2) * e + p + sp.Rational(17, 10) * v),
        "Kbound": (1 - b - p - g - e - 8 * tau, 1 - b - 8 * s + 15 * g + 23 * e + 3 * p + sp.Rational(36, 5) * v),
        "Delta_h": (hs + 4 * tau - lam / 2,
                    (b - sp.Rational(1, 2) + sp.Rational(7, 2) * s) - p - sp.Rational(13, 2) * g - 10 * e - sp.Rational(31, 10) * v),
        "Delta_k": (ks + 4 * tau - lam / 2,
                    (sp.Rational(7, 2) * s - b / 2) - 2 * p - sp.Rational(13, 2) * g - 10 * e - sp.Rational(31, 10) * v),
    }
    for name, (lhs, rhs) in checks.items():
        assert sp.expand(lhs - rhs) == 0, name
    return list(checks)


# ---------------------------------------------------------------------------
# 3. Random test of the covering argument
# ---------------------------------------------------------------------------


def covering_test(samples=200000, seed=1):
    """Random test of the covering argument of the block lemma.

    Returns (least excess saving, number of draws that pass the selection
    guards). Draws failing a guard (empty b-range, tau<=0 or lam<=0) are
    skipped and do not contribute to the minimum. This is a sanity check;
    the proof is the case analysis in the paper."""
    rng = random.Random(seed)
    worst = float("inf")
    used = 0
    for _ in range(samples):
        s = rng.uniform(0, 1 / 13)
        lo, hi = 5 * s, 0.5 - 1.5 * s
        if lo >= hi:
            continue
        b = rng.uniform(lo, hi)
        p, g, e = (rng.choice([0.0, rng.uniform(0, 0.1)]) for _ in range(3))
        v = rng.choice([0.0, rng.uniform(0, 0.3)])
        lam = 1 + s - 3 * g - 4 * e - v
        tau = s - 2 * g - 3 * e - p / 2 - 0.9 * v
        if tau <= 0 or lam <= 0:
            continue
        hs, ks = b + p, (1 - b) / 2
        Klow = 1 - b - p - g - e
        Dmax = 1 + s
        D = rng.uniform(lam, max(lam, Dmax))
        cuts = sorted(rng.random() for _ in range(3))
        degs = sorted([D * cuts[0], D * (cuts[1] - cuts[0]), D * (cuts[2] - cuts[1]), D * (1 - cuts[2])],
                      reverse=True)
        best = -float("inf")
        # bilinear: any nonempty proper subset S as N, complement as M
        for mask in range(1, 15):
            dN = sum(degs[i] for i in range(4) if mask >> i & 1)
            dM = D - dN
            save = min(dN / 2, (dM - hs) / 4, (dM - ks) / 4, Klow / 8)
            best = max(best, save)
        # one smooth variable (largest), others frozen
        dM = degs[0]
        save = min(dM - (1 + b + p - g - e) / 2, Klow / 2)
        best = max(best, save)
        # two smooth variables (two largest), others frozen
        dM, dN = degs[0], degs[1]
        if dM - hs > 0:
            save = min((dM + dN - 2 * hs) / 2, (dM - ks) / 2, Klow / 4)
            best = max(best, save)
        worst = min(worst, best - tau)
        used += 1
    assert used > 0 and worst > 0, (used, worst)
    return worst, used


# ---------------------------------------------------------------------------
# 4. Local facts about the kernel
# ---------------------------------------------------------------------------


def e(t, m):
    return cmath.exp(2j * math.pi * t / m)


def units(m):
    return [x for x in range(m) if math.gcd(x, m) == 1]


def kernel_direct(c, t):
    """K_t(c) = t^{-1} sum_{x,y units} e_t(x + y + c/(xy)), valid for prime powers t
    with the correction 1/(p(p-1)) when t = p is prime."""
    if math.gcd(c, t) != 1:
        return 0
    tot = 0
    for x in units(t):
        ix = pow(x, -1, t)
        for y in units(t):
            tot += e(x + y + c * ix * pow(y, -1, t), t)
    return tot / t


def characters(m):
    """All Dirichlet characters mod m as dictionaries (m small)."""
    U = units(m)
    # brute force: homomorphisms U -> C^*; find generators via sympy
    from sympy.ntheory import primitive_root
    chars = []
    phi = len(U)
    # use discrete log for prime powers of odd primes, brute otherwise
    fac = sp.factorint(m)
    gens = []
    for q, a in fac.items():
        t = q ** a
        if q == 2:
            if a == 1:
                continue
            if a == 2:
                gens.append((t, [(3 % t, 2)]))
            else:
                gens.append((t, [(t - 1, 2), (5, 2 ** (a - 2))]))
        else:
            gens.append((t, [(primitive_root(t), (q - 1) * q ** (a - 1))]))
    # local characters
    import itertools
    local_lists = []
    for t, gl in gens:
        Ut = units(t)
        # discrete log table
        table = {}
        exps = [range(o) for _, o in gl]
        for es in itertools.product(*exps):
            val = 1
            for (gg, _), ee in zip(gl, es):
                val = val * pow(gg, ee, t) % t
            table[val] = es
        loc = []
        for ks in itertools.product(*[range(o) for _, o in gl]):
            def chi(x, ks=ks, table=table, t=t, gl=gl):
                x %= t
                if math.gcd(x, t) != 1:
                    return 0
                es = table[x]
                return cmath.exp(2j * math.pi * sum(k * ee / o for k, ee, (_, o) in zip(ks, es, gl)))
            loc.append((t, chi))
        local_lists.append(loc)
    for combo in itertools.product(*local_lists):
        def chi(x, combo=combo):
            val = 1
            for _, c in combo:
                val *= c(x)
            return val
        chars.append(chi)
    assert len(chars) == phi
    return chars


def is_primitive(chi, m):
    for dd in sp.divisors(m):
        if dd == m:
            continue
        # chi induced from mod dd iff chi(x)=1 whenever x = 1 mod dd, (x,m)=1
        if all(abs(chi(x) - 1) < 1e-9 for x in units(m) if x % dd == 1 % dd):
            return False
    return True


def gauss(chi, m):
    return sum(chi(x) * e(x, m) for x in range(m))


def kernel_characters(v, d):
    tot = 0
    for chi in characters(d):
        if is_primitive(chi, d):
            tot += gauss(chi, d) ** 3 * chi(v).conjugate()
    return tot / (d * len(units(d)))


def local_checks():
    out = {}
    # prime formula and prime-power bound
    for p in (5, 7, 11):
        for c in (1, 2, 3):
            a = kernel_characters(c, p)
            b = kernel_direct(c, p) + 1 / (p * (p - 1))
            assert abs(a - b) < 1e-9
    worst = 0
    for t in (4, 8, 16, 9, 27, 25, 49, 81, 125):
        for c in units(t):
            val = kernel_direct(c, t)
            worst = max(worst, abs(val))
            if t in (4, 8, 9, 25, 27):
                assert abs(val - kernel_characters(c, t)) < 1e-8
    assert worst <= 9 + 1e-9
    out["max |K_{p^a}|"] = worst
    # Chinese remainder factorisation K_d(v) = prod_t K_t(v * (d/t)^{-3})
    for d in (15, 21, 35, 45):
        fac = sp.factorint(d)
        for v in units(d)[:5]:
            lhs = kernel_characters(v, d)
            rhs = 1
            for q, a in fac.items():
                t = q ** a
                D = d // t
                rhs *= kernel_characters(v * pow(D, -3, t) % t, t)
            assert abs(lhs - rhs) < 1e-8
    # Fourier transform at a prime: |sum_x K_p(cx) e_p(jx)| <= 2 sqrt p + 1, zero at j = 0
    for p in (101, 103):
        Kp = [0] + [kernel_direct(x, p) + 1 / (p * (p - 1)) for x in range(1, p)]
        for j in range(p):
            f = sum(Kp[x] * e(j * x, p) for x in range(p))
            if j == 0:
                assert abs(f) < 1e-8
            else:
                assert abs(f) <= 2 * math.sqrt(p) + 1 + 1e-8
    # Correlation sums at p = 101: generic affine maps give O(sqrt p),
    # the degenerate configurations give size about p.
    p = 101
    Kp = [0] + [kernel_direct(x, p) + 1 / (p * (p - 1)) for x in range(1, p)]

    def corr(maps, h):
        tot = 0
        for x in range(p):
            val = e(h * x, p)
            for (a, bb, conj) in maps:
                k = Kp[(a * (x + bb)) % p]
                val *= k.conjugate() if conj else k
            tot += val
        return abs(tot)

    rng = random.Random(5)
    big = 0
    for _ in range(40):
        a1, a2 = rng.randrange(1, p), rng.randrange(1, p)
        b1, b2 = rng.sample(range(p), 2)
        h = rng.randrange(p)
        big = max(big, corr([(a1, b1, False), (a2, b2, True)], h) / math.sqrt(p))
        n1, n2 = rng.sample(range(1, p), 2)
        if (n1 + n2) % p == 0:
            continue
        big = max(big, corr([(n1, b1, False), (n2, b1, True), (n1, b2, True), (n2, b2, False)], h) / math.sqrt(p))
    out["max correlation / sqrt p (generic)"] = big
    degenerate = corr([(3, 7, False), (3, 7, True)], 0) / p
    out["two equal maps / p"] = degenerate
    assert big < 12 and degenerate > 0.5
    return out


if __name__ == "__main__":
    inc, C = mass_increment()
    print("1. mass increment =", inc, "; C_6 = mu(U_6) (factorable stage) =", C, "=", sp.N(C, 25))
    print("2. exponent identities verified:", ", ".join(exponent_identities()))
    worst, used = covering_test()
    print("3. covering argument: 200000 parameter draws,", used, "pass the selection guards;",
          "least excess saving among them =", round(worst, 6))
    for k, v in local_checks().items():
        print("4.", k, "=", round(v, 4))
