"""Direct transcriptions of Gardam (2021, 2024) and Murray (2021).
Tuples (i,j,k,r) denote x^i y^j z^k r. Phase exponents are powers of zeta_8.
"""

from collections import Counter
from ring import ONE, convolution, reduce_mod


def field_pair(prime):
    # Sparse Laurent terms (coefficient, x-degree, y-degree, z-degree).
    def prod(a, b):
        return [(v * w, i + l, j + m, k + n) for v, i, j, k in a for w, l, m, n in b]

    one = [(1, 0, 0, 0)]
    x, X = [(1, 1, 0, 0)], [(1, -1, 0, 0)]
    y, Y = [(1, 0, 1, 0)], [(1, 0, -1, 0)]
    z, Z = [(1, 0, 0, 1)], [(1, 0, 0, -1)]
    neg = lambda a: [(-v, i, j, k) for v, i, j, k in a]
    if prime == 2:
        p = prod(prod(one + x, one + y), one + Z)
        q = prod(X, Y) + x + prod(Y, z) + z
        r = one + x + prod(Y, z) + prod(prod(x, y), z)
        s = one + prod(x + X + y + Y, Z)
    elif prime == 3:
        p = prod(prod(one + x, one + y), Z + neg(z))
        q = prod(prod(one + x, X + Y), one + neg(Z)) + prod(one + Y, z + neg(Z))
        r = prod(prod(one + Y, x + y), z + neg(one)) + prod(one + x, z + neg(Z))
        s = neg(z) + prod(one + x + X + y + Y, Z + neg(one))
    else:
        raise ValueError(prime)
    u, v = Counter(), Counter()
    for rep, block in enumerate((p, q, r, s)):
        for c, i, j, k in block:
            u[i, j, k, rep] += c
            # Gardam's prescribed inverse, also used by Murray.
            if rep == 0:
                v[i - 1, -j, -k, rep] += c
            elif rep == 1:
                v[i - 1, j, k, rep] -= c
            elif rep == 2:
                v[i, j - 1, k, rep] -= c
            else:
                v[i, -j, -k - 1, rep] += c
    u, v = reduce_mod(u, prime), reduce_mod(v, prime)
    assert (
        reduce_mod(convolution(u, v), prime)
        == reduce_mod(convolution(v, u), prime)
        == ONE
    )
    return u, v


def cyclotomic_pair():
    # Set s=t=zeta_8 in Theorem A. Negative signs add four to a phase.
    # Each block lists x,y,z exponents then the TOTAL phase (including s,t).
    u = [
        [(0, 0, 0, 0), (1, 0, -1, 2), (-1, 0, -1, 6), (0, 1, -1, 6), (0, -1, -1, 2)],
        [(-1, 0, 0, 7), (0, 0, 0, 1), (-1, -1, 1, 5), (0, 1, 1, 3)],
        [(-1, -1, 1, 1), (1, 0, 1, 7), (0, -1, 2, 3), (0, 0, 2, 5)],
        [
            (-1, 0, -1, 0),
            (0, 1, -1, 0),
            (0, 0, -1, 6),
            (-1, 1, -1, 2),
            (-1, 0, -2, 4),
            (0, 1, -2, 4),
            (0, 0, -2, 6),
            (-1, 1, -2, 2),
        ],
    ]
    v = [
        [(0, 0, 0, 0), (-1, 0, 1, 2), (1, 0, 1, 6), (0, 1, 1, 2), (0, -1, 1, 6)],
        [(0, 0, 0, 5), (-1, 0, 0, 3), (0, 1, 1, 7), (-1, -1, 1, 1)],
        [(-1, -1, 1, 5), (1, 0, 1, 3), (0, -1, 2, 7), (0, 0, 2, 1)],
        [
            (-1, 1, 0, 6),
            (0, 0, 0, 2),
            (0, 1, 0, 0),
            (-1, 0, 0, 0),
            (-1, 1, 1, 6),
            (0, 0, 1, 2),
            (0, 1, 1, 4),
            (-1, 0, 1, 4),
        ],
    ]
    return [
        {(i, j, k, r): e for r, block in enumerate(side) for i, j, k, e in block}
        for side in (u, v)
    ]
