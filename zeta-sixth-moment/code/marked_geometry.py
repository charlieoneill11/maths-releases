"""Integrate 9! times the squared Schur target on the new marked regions.

Coordinates are (x, k=x+y, z). A row (a,b,c,d) represents ax+bk+cz+d >= 0.
All vertex, face, volume, and polynomial computations use rational arithmetic.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations
from math import factorial, prod


def determinant(a, b, c):
    return sum(
        a[i] * (b[(i + 1) % 3] * c[(i + 2) % 3] - b[(i + 2) % 3] * c[(i + 1) % 3])
        for i in range(3)
    )


def difference(a, b):
    return tuple(x - y for x, y in zip(a, b))


def value(row, vertex):
    return sum(a * x for a, x in zip(row[:3], vertex)) + row[3]


def vertices(rows):
    result = set()
    for planes in combinations(rows, 3):
        columns = list(zip(*planes))
        denominator = determinant(*columns[:3])
        if denominator == 0:
            continue
        vertex = []
        for index in range(3):
            numerator_columns = columns[:3].copy()
            numerator_columns[index] = columns[3]
            vertex.append(Fraction(-determinant(*numerator_columns), denominator))
        if all(value(row, vertex) >= 0 for row in rows):
            result.add(tuple(vertex))
    return sorted(result)


def center(points):
    return tuple(sum(column) / len(points) for column in zip(*points))


def triangulate_face(points, face):
    """Order a convex face about its center using a nondegenerate coordinate projection."""
    midpoint = center([points[index] for index in face])
    for a, b in combinations(range(3), 2):
        positions = {i: (points[i][a] - midpoint[a], points[i][b] - midpoint[b]) for i in face}

        def cross(i, j):
            x, y = positions[i]
            u, v = positions[j]
            return x * v - y * u

        if any(cross(i, j) for i, j in combinations(face, 2)):
            break
    else:
        return []

    def compare(i, j):
        def lower_half(index):
            x, y = positions[index]
            return y < 0 or (y == 0 and x < 0)

        if lower_half(i) != lower_half(j):
            return 1 if lower_half(i) else -1
        area = cross(i, j)
        return (area < 0) - (area > 0)

    ordered = sorted(face, key=cmp_to_key(compare))
    return [(ordered[0], ordered[j], ordered[j + 1]) for j in range(1, len(face) - 1)]


def tetrahedron_mass(points):
    """Dirichlet's barycentric monomial integral cancels the target factor 9!."""
    volume_factor = abs(determinant(*(difference(p, points[3]) for p in points[:3])))
    linear_factors = [
        [z - k + x for x, k, z in points],
        [z - x for x, k, z in points],
        [k - 2 * x for x, k, z in points],
    ]
    polynomial = {(0, 0, 0, 0): Fraction(1)}
    for factor in linear_factors * 2:
        expanded = defaultdict(Fraction)
        for powers, coefficient in polynomial.items():
            for index, entry in enumerate(factor):
                new_powers = list(powers)
                new_powers[index] += 1
                expanded[tuple(new_powers)] += coefficient * entry
        polynomial = expanded
    moment = sum(c * prod(factorial(e) for e in power) for power, c in polynomial.items())
    return volume_factor * moment / 4


def mass(rows):
    points = vertices(rows)
    if len(points) < 4 or not any(
        determinant(*(difference(p, points[0]) for p in triple))
        for triple in combinations(points[1:], 3)
    ):
        return Fraction(0)
    faces = {tuple(i for i, p in enumerate(points) if value(row, p) == 0) for row in rows}
    triangles = [t for f in sorted(faces) if len(f) >= 3 for t in triangulate_face(points, f)]
    incidences = Counter(tuple(sorted(edge)) for t in triangles for edge in combinations(t, 2))
    assert set(incidences.values()) == {2}
    assert len(points) - len(incidences) + len(triangles) == 2
    midpoint = center(points)
    return sum(tetrahedron_mass([points[i] for i in t] + [midpoint]) for t in triangles)


def reflected(row):
    # J(x,k,z)=(1-z,2-k+x-z,1-x).
    a, b, c, d = row
    return (b - c, -b, -a - b, a + 2 * b + c + d)


def reversed_side(row):
    return tuple(-v for v in row)


def increments():
    chamber = [(1, 0, 0, 0), (-2, 1, 0, 0), (1, -1, 1, 0), (0, 0, -1, 1)]
    marked = [(0, -1, 1, 0), (-2, 0, 2, -1), (-18, -64, 50, 7)]
    outside_triangle = (0, 2, 0, -1)
    outside_old_cap = (0, 1, -2, 1)
    outside_old_mixed = [
        [(1, 0, 1, -1), (5, 0, -3, 1)],
        [(-1, 0, -1, 1), (3, 0, -5, 3)],
    ]
    old_strip = [marked[0], (0, 0, 50000000, -25000001), (0, -61, -40, 51)]
    old_box = [
        (100, 0, 0, -17), (-1000, 0, 0, 171),
        (0, 100000000, 0, -50000001), (0, -50000000, 0, 25000001),
        (0, 0, 100, -53), (0, 0, -50, 27),
    ]
    base = chamber + [outside_triangle, outside_old_cap] + marked
    high_trace = [(0, 4, 4, -5), (0, -2, -2, 3)]
    low_trace = [(0, 1, 1, -1), (0, -4, -4, 5)]
    direct = Fraction(0)
    for cell in outside_old_mixed:
        lower = base + low_trace + cell
        direct += mass(base + high_trace + cell)
        direct += mass(lower) - mass(lower + old_strip) - mass(lower + old_box)
        direct += mass(lower + old_strip + old_box)

    whole_trace = [low_trace[0], high_trace[1]]
    other_orientation = chamber + whole_trace + [outside_triangle] + list(map(reflected, marked))
    extra = Fraction(0)
    # z-x > 1/2 survives reflection. These two cells partition failure of the direct mark.
    for cell in outside_old_mixed:
        for failure in [[reversed_side(marked[0])], [marked[0], reversed_side(marked[2])]]:
            region = other_orientation + cell + failure
            extra += mass(region) - mass(region + old_strip)
    return 2 * direct, 2 * extra


if __name__ == "__main__":
    direct, reflected_extra = increments()
    assert reflected_extra == Fraction(2694730153181958183923554025, 7494788633706744652348002376704)
    print("Direct gain, including its reflection:", direct, float(direct))
    print("Extra gain from combining both orientations:", reflected_extra, float(reflected_extra))
