"""Exact certificate replay using elementary Klein-bottle multiplication over Z.

The JSON words encode finite integer elements by the coefficient formula
in the README. This pass verifies the vertex identities, both cleared
integer products, the pole-proof hypotheses, and the coefficient bound.
"""

from collections import Counter
from functools import cache, reduce
from itertools import groupby
import json
from math import comb
from pathlib import Path

DATA = json.loads(Path(__file__).with_name("integral-pair.json").read_text())
ONE = {(0, 0, 0): 1}


def mul(left, right):
    out = Counter()
    for (i, j, e), a in left.items():
        for (k, transverse, f), b in right.items():
            out[i + k + e * f, j + (-1) ** e * transverse, e ^ f] += a * b
    return {g: c for g, c in out.items() if c}


def power(a, e):
    return reduce(mul, [a] * e, ONE)


def vertex(m, inverse, half=False):
    d = m // 2
    phases = DATA["phases"][:4] if half else DATA["phases"]
    if inverse:
        phases = [(-s, n) for s, n in reversed(phases)]
    out = ONE if half and not inverse else {(-4 * d, 0, 0): 1}
    for s, n in phases:
        atom = {(i, 0, 0): 1 for i in range(d + 1)}
        atom.update({(i, n, 1): s for i in range(d)})
        out = mul(out, atom)
    return out


def check_vertex(m):
    d = m // 2
    F = {(i - d, 0, 0): 1 for i in range(m)}
    for half in (False, True):
        n, adj = (vertex(m, inv, half) for inv in (False, True))
        assert mul(n, adj) == mul(adj, n) == power(F, 4 if half else 8)
    for inv in (False, True):
        n = vertex(m, inv)
        scalar = {(i, j): c for (i, j, e), c in n.items() if e == 0}
        assert {(-i, j): c for (i, j), c in scalar.items()} == scalar
        at_one = Counter()
        for (i, j), c in scalar.items():
            at_one[i, 0, 0] += c
        assert {i: c for i, c in at_one.items() if c} == power(F, 4)
        screw = {(i, j): c for (i, j, e), c in n.items() if e == 1}
        assert screw
        # Shift exponents to nonnegative integers, then take Taylor coefficients.
        base = min(j for i, j in screw)
        for order in range(5):
            derivative = Counter()
            for (i, j), c in screw.items():
                derivative[i] += c * comb(j - base, order)
            assert not any(derivative.values())


def inverse(w):
    return [-x for x in reversed(w)]


def cancel(word):
    stack = []
    norms = Counter()
    for x in word:
        if stack and stack[-1] == -x:
            stack.pop()
            norms[abs(x)] += 8
        else:
            stack.append(x)
    return stack, norms


def comm(u, v):
    return cancel(u + v + inverse(u) + inverse(v))[0]


def dihedral_extremes(word):
    """Return exact integral coefficients at the two extremes of the longest site."""
    from verify import AA, BB, IDENT, REPS, TRANSLATIONS, compose
    from verify import power as group_power

    @cache
    def letter(j):
        m, _, k = DATA["vertices"][abs(j) - 1]
        return {(i, k * n, e): c for (i, n, e), c in vertex(m, j < 0).items()}

    results = []
    for choose, orientation in ((min, -1), (max, 1)):
        site, coefficient, length = IDENT, 1, 0
        for b_type, letters in groupby(word, lambda j: abs(j) == 3):
            layer = reduce(mul, map(letter, letters), ONE)
            candidates = []
            for (i, j, e), value in layer.items():
                if e == 0:
                    continue
                x, y = (j, i) if b_type else (i, j)
                translation = compose(
                    group_power(TRANSLATIONS[0], x), group_power(TRANSLATIONS[1], y)
                )
                step = compose(translation, BB if b_type else AA)
                candidates.append((compose(site, step), value))
            site, value = choose(candidates, key=lambda term: term[0][1][:2])
            coefficient *= value
            length += 1
        signs, displacement = site
        r = next(i for i, (s, _) in enumerate(REPS) if s == signs)
        x, y, z = (a - b for a, b in zip(displacement, REPS[r][1]))
        assert all(n % 2 == 0 for n in (x, y, z))
        # The centered denominator has coefficient one at both extreme monomials.
        results.append(
            (
                (x // 2 - orientation * 208, y // 2 - orientation * 112, -z // 2, r),
                coefficient,
            )
        )
        assert length == 57
    return results


def certificate():
    assert DATA["vertices"] == [[3, "a", 3], [5, "a", 3], [3, "b", 15]]
    for m in (3, 5):
        check_vertex(m)
    print(
        "both vertex norm products, both half norms, reciprocal scalars and fifth-order screw zeros verified"
    )
    w, z = comm([1], [3]), comm([2], [3])
    u, v = DATA["u"], DATA["v"]
    assert u == comm(comm(comm(w, z), w), w)
    assert v == inverse(u)
    exps = DATA["centered_denominator_powers"]
    for word in (u, v):
        assert [4 * word.count(i) + 4 * word.count(-i) for i in (1, 2, 3)] == exps
    for name, word in (("uv", u + v), ("vu", v + u)):
        rem, powers = cancel(word)
        assert not rem and [powers[i] for i in (1, 2, 3)] == [2 * e for e in exps]
        print(
            name,
            "cleared integer product = D^2; centered divisor exponents",
            list(2 * e for e in exps),
        )

    for name, word, sign in (("u", u, 1), ("v", v, -1)):
        ends = dihedral_extremes(word)
        assert ends == [
            ((-1420, -208, 14, 1), sign * 2187),
            ((1419, 202, 14, 1), -sign * 2187),
        ]
        print(name, "exact extreme coefficients", ends)

    # A centered numerator contributes at most 8*61+16 doubled
    # displacement in either coordinate. Translation to a left coset
    # representative changes doubled displacement by at most two.
    directions = [(m, k, j) for m, _, k in DATA["vertices"] for _, j in DATA["phases"]]
    assert all(2 * max(m // 2, abs(k * j)) + 1 <= 61 for m, k, j in directions)
    assert max(8 * (m // 2) for m, k, j in directions) <= 16
    shifts = (exps[0] + 2 * exps[1], exps[2])
    assert shifts == (208, 112)
    assert all(
        (8 * 61 + 16) * len(word) + 2 * max(shifts) + 2 < 2 * DATA["coordinate_bound"]
        for word in (u, v)
    )
    print("finite coefficient formula bound checked for both 64-letter words")


if __name__ == "__main__":
    certificate()
