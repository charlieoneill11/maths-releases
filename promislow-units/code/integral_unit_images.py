"""Read both certificate words independently in exact representations of P."""

import json
from pathlib import Path
from flint import fmpq_mat

from verify import AA, BB, REPS, compose


def identity(n):
    return fmpq_mat([[int(i == j) for j in range(n)] for i in range(n)])


def power(a, n):
    return a**n if n >= 0 else a.inv() ** (-n)


def representation(g, coords):
    d = coords[0].nrows()
    out = fmpq_mat(4 * d, 4 * d)
    for j, r in enumerate(REPS):
        signs, trans = compose(g, r)
        i = next(i for i, (s, _) in enumerate(REPS) if s == signs)
        diff = [v * (u - w) for v, u, w in zip(signs, trans, REPS[i][1])]
        assert all(t % 2 == 0 for t in diff)
        block = identity(d)
        for mat, e in zip(coords, (diff[0] // 2, diff[1] // 2, -diff[2] // 2)):
            block = block * power(mat, e)
        for r in range(d):
            for c in range(d):
                out[d * i + r, d * j + c] = block[r, c]
    return out


def evaluate(coords, data):
    a, b = (representation(g, coords) for g in (AA, BB))
    one = identity(a.nrows())
    assert b.inv() * a**2 * b == power(a, -2) and a.inv() * b**2 * a == power(b, -2)
    letters = {}
    for j, (m, axis, k) in enumerate(data["vertices"], 1):
        h, other = (a, b) if axis == "a" else (b, a)
        t, w = h * h, other * other
        p = sum((t**i for i in range(m // 2 + 1)), start=one - one)
        q = sum((t**i for i in range(m // 2)), start=one - one)
        den = (p * p - t * q * q) ** 4
        for sign in (1, -1):
            terms = data["phases"] if sign == 1 else reversed(data["phases"])
            value = den.inv()
            for s, n in terms:
                value = value * (p + sign * s * q * power(w, k * n) * h)
            letters[sign * j] = value
        assert letters[j] * letters[-j] == letters[-j] * letters[j] == one
    results = []
    for w in (data["u"], data["v"]):
        result = one
        for j in w:
            result = result * letters[j]
        results.append(result)
    u, v = results
    assert u * v == v * u == one
    blocksize = coords[0].nrows()
    twists = (1, -1, 1, -1)
    sign = fmpq_mat(
        [
            [twists[i // blocksize] * int(i == j) for j in range(4 * blocksize)]
            for i in range(4 * blocksize)
        ]
    )
    h, hinv = u * sign * v * sign, sign * u * sign * v
    assert h * hinv == hinv * h == one
    return u, v, h, hinv


def residue(x, n):
    return int(x.numerator) * pow(int(x.denominator), -1, n) % n


def run():
    data = json.loads(Path(__file__).with_name("integral-pair.json").read_text())
    rational = [fmpq_mat([[v]]) for v in (2, 3, 5)]
    u, v, h, _ = evaluate(rational, data)
    for name, mat, expected in (
        ("u", u, [11, 15, 3, 9]),
        ("v", v, [8, 2, 14, 8]),
        ("sign pair", h, [12, 16, 0, 2]),
    ):
        row = [residue(mat[0, j], 17) for j in range(4)]
        assert row == expected
        print(name, "first row modulo 17:", row)
    for mat in (u, v):
        for n in mat.entries():
            den = int(n.denominator)
            for p in (2, 3, 5):
                while den % p == 0:
                    den //= p
            assert den == 1
    # Integral unit T with irreducible cubic modulo two, a generator of F8* there.
    t = fmpq_mat([[0, 0, -1], [1, 0, -1], [0, 1, 0]])
    u, v, h, hi = evaluate((t, t**2, t**3), data)
    for n in (2, 4, 8):
        for mat in (u, v, h, hi):
            assert all(int(e.denominator) == 1 for e in mat.entries())
        occupied = [
            j
            for j in range(4)
            if any(residue(u[r, 3 * j + c], n) for r in range(3) for c in range(3))
        ]
        assert len(occupied) > 1
        differences = sum(
            bool(residue(h[i, j] - int(i == j), n))
            for i in range(12)
            for j in range(12)
        )
        if n == 2:
            assert differences == 0
        print(
            "modulus",
            n,
            "u block-row sites",
            occupied,
            "sign-pair entries differing from identity",
            differences,
        )


if __name__ == "__main__":
    run()
