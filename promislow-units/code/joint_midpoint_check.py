"""Check the local divisibilities directly in faithful Laurent matrices over Z.

Run with python-flint. Each of the twelve divisions is an ordinary exact
polynomial remainder computation for every entry of a four-by-four matrix.
"""

from argparse import ArgumentParser
from dataclasses import dataclass
from functools import cache

from flint import fmpz_mpoly_ctx

from verify import AA, BB, IDENT, REPS, compose, power

CTX = fmpz_mpoly_ctx.get(("X", "Y", "Z"))
VARIABLES = CTX.gens()
ZERO = CTX.constant(0)


def monomial(exponents):
    return CTX.from_dict({tuple(exponents): 1})


@dataclass
class Matrix:
    # Actual matrix = Laurent monomial with these exponents times entries.
    shift: tuple
    entries: list

    def __mul__(self, other):
        shift = tuple(a + b for a, b in zip(self.shift, other.shift))
        entries = [
            [
                sum((a * b for a, b in zip(row, col) if a and b), ZERO)
                for col in zip(*other.entries)
            ]
            for row in self.entries
        ]
        return Matrix(shift, entries)

    def __neg__(self):
        return Matrix(self.shift, [[-a for a in row] for row in self.entries])

    def __add__(self, other):
        shift = tuple(map(min, zip(self.shift, other.shift)))
        f, g = (
            monomial(a - b for a, b in zip(s, shift)) for s in (self.shift, other.shift)
        )
        return Matrix(
            shift,
            [
                [f * a + g * b for a, b in zip(r, t)]
                for r, t in zip(self.entries, other.entries)
            ],
        )

    def __pow__(self, n):
        assert n >= 0
        if n == 0:
            return ONE
        if n == 1:
            return self
        half = self ** (n // 2)
        square = half * half
        return square * self if n % 2 else square


@cache
def group(g):
    # On the right module basis r, g r_j = r_i x^u y^v z^w.
    sites = {}
    for j, r in enumerate(REPS):
        sign, displacement = compose(g, r)
        i = next(i for i, (s, _) in enumerate(REPS) if s == sign)
        diff = [s * (a - b) for s, a, b in zip(sign, displacement, REPS[i][1])]
        assert all(v % 2 == 0 for v in diff)
        sites[i, j] = diff[0] // 2, diff[1] // 2, -diff[2] // 2
    shift = tuple(map(min, zip(*sites.values())))
    return Matrix(
        shift,
        [
            [
                monomial(a - b for a, b in zip(sites[i, j], shift))
                if (i, j) in sites
                else ZERO
                for j in range(4)
            ]
            for i in range(4)
        ],
    )


ONE = group(IDENT)
NULL = Matrix((0, 0, 0), [[ZERO] * 4 for _ in range(4)])
PHASES = ((-1, 0), (1, -1), (-1, -2), (1, -1), (1, 0), (-1, -1), (1, -2), (-1, -1))
VERTICES = ((3, AA, BB, 3), (5, AA, BB, 3), (3, BB, AA, 15))


def scalar(shift, polynomial):
    return Matrix(
        shift, [[polynomial if i == j else ZERO for j in range(4)] for i in range(4)]
    )


@cache
def divisor(j):
    m, h, _, _ = VERTICES[j]
    axis = 0 if h == AA else 1
    x = VARIABLES[axis]
    shift = [0, 0, 0]
    shift[axis] = -(m // 2)
    return scalar(tuple(shift), sum((x**i for i in range(m)), ZERO))


@cache
def numerator(j, inverse=False, half=False):
    m, h, other, k = VERTICES[j]
    d = m // 2
    p = sum((group(power(h, 2 * i)) for i in range(d + 1)), start=NULL)
    q = sum((group(power(h, 2 * i)) for i in range(d)), start=NULL)
    phases = PHASES[:4] if half else PHASES
    if inverse:
        phases = [(-s, n) for s, n in reversed(phases)]
    # The first four raw atoms give C. All other numerators use the centered divisor.
    result = ONE if half and not inverse else group(power(h, -8 * d))
    for sign, n in phases:
        screw = q * group(compose(power(other, 2 * k * n), h))
        result = result * (p + (screw if sign == 1 else -screw))
    return result


def product(matrices):
    result = ONE
    for mat in matrices:
        result = result * mat
    return result


def check_norms():
    for j in range(3):
        for half in (False, True):
            a, b = numerator(j, False, half), numerator(j, True, half)
            den = divisor(j) ** (4 if half else 8)
            for product_ab in (a * b, b * a):
                assert all(not p for row in (product_ab + -den).entries for p in row)
    print(
        "three full and three half numerators: both Laurent matrix norm products verified",
        flush=True,
    )


def check(prime, vertex, inverse):
    w = [(vertex, False), (2, False), (vertex, True), (2, True)]
    if inverse:
        w = [(j, not inv) for j, inv in reversed(w)]
    conjugate = product(
        [
            numerator(prime, True, True),
            *(numerator(j, inv) for j, inv in w),
            numerator(prime, False, True),
        ]
    )
    den = divisor(prime) ** 4 * divisor(vertex) ** 8 * divisor(2) ** 8
    diff = conjugate + -den
    e = 5 + 8 * (prime in (vertex, 2))
    factor = divisor(prime).entries[0][0] ** e
    assert all(not (p % factor) for row in diff.entries for p in row)
    print(
        f"prime {prime + 1}, W{vertex + 1}, inverse={inverse}: all entries divisible through power {e}",
        flush=True,
    )


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, choices=(1, 2, 3))
    args = parser.parse_args()
    check_norms()
    for j in range(3) if args.prime is None else (args.prime - 1,):
        for i in range(2):
            for inv in (False, True):
                check(j, i, inv)
