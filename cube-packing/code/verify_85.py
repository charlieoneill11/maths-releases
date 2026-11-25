"""Finite step in the proof that alpha(C_85 strong-cubed) <= 75,821.

Run with Python 3.9 or newer. All coordinates are starting corners of
dual slabs. The accompanying README gives the reduction to the 81,920 cases.
"""

from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations, product
from math import gcd

SIDE = 85
FULL_LINE_SIZE = 42
HEIGHTS = (17, 34, 51, 68)
CLASS_THREE_SLOPES = (6, -6, 14, -14)
AXES = (0, 1, 2)


def maximum_line(hole):
    """Independent centers on an 85-cycle when {hole, hole+1} is empty."""
    return frozenset((hole + 2 * k) % SIDE for k in range(1, FULL_LINE_SIZE + 1))


LINES = tuple(maximum_line(h) for h in range(SIDE))


@lru_cache(None)
def planar_centers(slope):
    """Reconstruct a classified full plane with hole graph v = slope*u."""
    centers = set()
    for v in range(SIDE):
        counts = [int(v in LINES[slope * u % SIDE]) for u in range(SIDE)]
        # The two physical rows covering a dual row of count zero are empty at v.
        first = counts.index(0)
        occupied = 0
        for step in range(SIDE):
            u = (first + step) % SIDE
            assert occupied in (0, 1)
            if occupied:
                centers.add((u, v))
            occupied = counts[u] - occupied
        assert occupied == 0

    assert len(centers) == 21 * SIDE
    for u, v in product(range(SIDE), repeat=2):
        count = sum(((u + du) % SIDE, (v + dv) % SIDE) in centers
                    for du, dv in product((0, 1), repeat=2))
        assert count == int(v != slope * u % SIDE)
    return centers


@dataclass(frozen=True)
class Slab:
    axis: int
    height: int
    slope: int
    intercept: int

    @property
    def planar_axes(self):
        return tuple(i for i in AXES if i != self.axis)

    def hole(self, known_axis, coordinate):
        """Remaining coordinate of the hole on one dual line."""
        u, _ = self.planar_axes
        if known_axis == u:
            return (self.slope * coordinate + self.intercept) % SIDE
        return pow(self.slope, -1, SIDE) * (coordinate - self.intercept) % SIDE

    def center(self, first_axis, first, second):
        """Is the physical projected point present in this full slab?"""
        u, _ = self.planar_axes
        a, b = (first, second) if first_axis == u else (second, first)
        return (a % SIDE, (b - self.intercept) % SIDE) in planar_centers(self.slope)


def candidate_slabs(a, b, c, axis):
    """Lift each slope of z = a*x + b*y + c over F_5 to its two real options."""
    inverse_b = pow(b, -1, 5)
    options = []
    for height in HEIGHTS:
        t = height // 17
        slope, intercept = ((b, a * t + c), (a, b * t + c),
                            (-a * inverse_b, (t - c) * inverse_b))[axis]
        pair = tuple(Slab(axis, height, s, 17 * (intercept % 5))
                     for s in CLASS_THREE_SLOPES if (s - slope) % 5 == 0)
        assert len(pair) == 2
        options.append(pair)
    return options


@lru_cache(None)
def allows_neighbor(base, transverse, direction):
    """Test four already-pinned dual lines of a putatively almost-full neighbor."""
    i = base.axis
    j = transverse[0].axis
    k = 3 - i - j
    shared = base.height + int(direction > 0)
    neighbor = base.height + direction
    bad = set()
    for pin in transverse:
        # This transverse full slab forces an empty dual cube at (neighbor,u,pin.height).
        u = pin.hole(i, neighbor)
        proposed = LINES[pin.height]
        base_column = LINES[base.hole(k, u)]
        for other in transverse:
            if other == pin:
                continue
            h = other.height
            if other.hole(i, neighbor) == u:
                bad.add(u)
                break
            if not (other.center(i, shared, u) or other.center(i, shared, u + 1)):
                continue
            # Both i-slabs must see the same physical j-coordinate of this point.
            observed = base_column.intersection((h, h + 1))
            assert len(observed) == 1
            if observed.isdisjoint(proposed):
                bad.add(u)
                break
    return len(bad) <= 2


def verify_arithmetic():
    steps = (2, 6, 14, 42)
    assert len({s % 17 for s in (*steps, *(-v for v in steps))}) == 8
    assert all(gcd(SIDE, 1 + sign * a * b * c) != SIDE
               for a, b, c in product(steps, repeat=3) for sign in (-1, 1))
    possible = {tuple(sorted((a, b, c))) for a, b, c in product(steps, repeat=3)
                if any((1 + s * a * b * c) % 17 == 0 for s in (-1, 1))}
    assert possible == {(2, 14, 14), (6, 6, 42)}
    assert [(42 * a + 42) % SIDE - 42 for a in steps] == [-1, -3, -7, -21]


def verify():
    verify_arithmetic()
    shapes = Counter()
    survivors = 0
    for a, b, c in product((-1, 1), (-1, 1), range(5)):
        variants = [list(product(*candidate_slabs(a, b, c, axis))) for axis in AXES]
        for planes in product(*variants):
            shapes[a, b, c] += 1
            possible = all(
                allows_neighbor(base, planes[j], direction)
                for i, j in permutations(AXES, 2)
                for base in planes[i] for direction in (-1, 1)
            )
            survivors += int(possible)
    assert len(shapes) == 20 and set(shapes.values()) == {4096}
    print(f"{sum(shapes.values()):,} configurations checked; {survivors} survive.")
    if survivors:
        raise SystemExit(1)


if __name__ == "__main__":
    verify()
