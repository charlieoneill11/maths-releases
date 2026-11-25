"""Check the maximum-support atlas and integer branching certificates, without an LP solver."""
from collections import Counter
from gzip import open as gzip_open
from itertools import combinations, product
import json
from pathlib import Path

ROOT = Path(__file__).parent
POINTS = tuple(product(range(7), repeat=3))
SITES = tuple(range(343))
BANDS = [{i for i, p in enumerate(POINTS) if (p[a]-t) % 7 < 2}
         for a in range(3) for t in range(7)]
STRIPS = [BANDS[7*a+t] & BANDS[7*b+u] for a, b in combinations(range(3), 2)
          for t, u in product(range(7), repeat=2)]
CUBES = [BANDS[x] & BANDS[7+y] & BANDS[14+z] for x, y, z in POINTS]
GEOMETRY = [(s, bound) for family, bound in [(CUBES, 3), (STRIPS, 9), (BANDS, 31)] for s in family]


def augmented_rows(points, threshold):
    # Inputs y(0..342), t(343..375) are unit-box variables. Residual mass is 3y.
    triple = {p: 343+i for i, p in enumerate(sorted(points))}
    def row(y, t, rhs, a=1, b=1):
        return [(p,3*a) for p in y]+[(triple[p],b) for p in t], rhs

    yield row(SITES, points, -106, -1, -3)
    yield row((), points, -threshold, b=-1)
    yield [], 0
    for p in sorted(points):
        yield row([p], [p], -1, -1, -1)
    for p in SITES:
        yield row([p], points & {p}, 2, 1, 2)
    for s, limit in GEOMETRY:
        yield row(s, points & s, limit, 1, 3)


def heavy_rows(points):
    # Every site of the maximum independent set is at least double. All other
    # sites have multiplicity 0 or 1. The remaining occupancy bit at every
    # site of the torus is integral and at most 1.
    yield [(p, -1) for p in SITES], -40
    for s, limit in GEOMETRY:
        yield [(p, 1) for p in s], limit-2*len(points & s)


def check_tree(tree, rows, fixed, offset, dimension):
    if len(tree) == 3:
        site, left, right = tree
        index = site+offset
        assert type(site) is int and offset <= index < dimension and index not in fixed
        fixed[index] = 0
        n = check_tree(left, rows, fixed, offset, dimension)
        fixed[index] = 1
        n += check_tree(right, rows, fixed, offset, dimension)
        del fixed[index]
        return n
    assert len(tree) % 2 == 0
    coefficient = [0]*dimension
    upper = 0
    for i, price in zip(tree[::2], tree[1::2]):
        assert type(i) is int and 0 <= i < len(rows) and type(price) is int and price > 0
        terms, rhs = rows[i]
        upper += price*rhs
        for j, value in terms:
            coefficient[j] += price*value
    lower = sum(value*fixed[j] if j in fixed else min(0,value) for j,value in enumerate(coefficient))
    assert lower > upper
    return 1


def main():
    atlas = []
    for line in ROOT.joinpath('atlas.tsv').read_text().splitlines():
        layers = tuple(map(int, line.split()))
        assert len(layers)==7 and all(0 <= v < 1 << 49 for v in layers)
        points = {i for i in SITES if layers[i//49] & (1 << (i%49))}
        assert len(points)==33 and all(len(points & cube) <= 1 for cube in CUBES)
        atlas.append(points)
    assert len(atlas)==len({frozenset(s) for s in atlas})==1016
    with gzip_open(ROOT/'prices.json.gz', 'rt') as f:
        certificates = json.load(f)
    threshold = certificates['threshold']
    assert threshold == 16
    for name, dimension, offset in [('augmented',376,343), ('heavy',343,0)]:
        trees = certificates[name]
        assert len(trees)==len(atlas)
        leaves=0
        for points, tree in zip(atlas,trees):
            rows = list(augmented_rows(points,threshold) if name=='augmented' else heavy_rows(points))
            leaves += check_tree(tree, rows, {}, offset, dimension)
        print(f'{name}: {len(trees)} maximum supports, {leaves} integer-price leaves.')


if __name__=='__main__':
    main()
