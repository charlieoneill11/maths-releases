"""Compute the retained coefficient on the union of S and z-x > 1/2.

Use the complement in the ordered unit chamber. Reflection exchanges the
two central trace halves, so it suffices to integrate 1 <= k+z <= 3/2,
where k=x+y. Plane boundaries have zero mass.
"""

from fractions import Fraction

from marked_geometry import mass


def spread_coefficient():
    # Each row specifies ax+bk+cz+d >= 0 in the coordinates (x,k,z).
    narrow_gap = [
        (1, 0, 0, 0),         # x >= 0
        (-2, 1, 0, 0),        # y >= x
        (1, -1, 1, 0),        # z >= y
        (0, 0, -1, 1),        # z <= 1
        (0, 1, 1, -1),        # k+z >= 1
        (0, -2, -2, 3),       # k+z <= 3/2
        (0, 2, 0, -1),        # exclude the old triangle k < 1/2
        (2, 0, -2, 1),        # z-x <= 1/2
    ]
    # In this half the reflected triangle would need y+z > 3/2.
    # The old mixed test costs at least 4(1-z+x) >= 2. Of the
    # remaining old tests, only the direct cubic strip and box meet it.
    cubic_strip = [
        (0, -1, 1, 0),                 # k <= z
        (0, 0, 50_000_000, -25_000_001), # z >= .50000002
        (0, -61, -40, 51),             # 40(k+z) + 21k <= 51
    ]
    old_box = [
        (100, 0, 0, -17), (-1000, 0, 0, 171),            # .170 <= x <= .171
        (0, 100_000_000, 0, -50_000_001),                # k >= .50000001
        (0, -50_000_000, 0, 25_000_001),                 # k <= .50000002
        (0, 0, 100, -53), (0, 0, -50, 27),               # .53 <= z <= .54
    ]
    raw_gap = mass(narrow_gap)
    assert raw_gap == Fraction(209, 1024)
    assert mass(narrow_gap + cubic_strip + old_box) == 0

    lower_gap = raw_gap - mass(narrow_gap + cubic_strip) - mass(narrow_gap + old_box)
    return 42 - 2 * lower_gap


def rounded_down(number, places):
    scale = 10**places
    integral, remainder = divmod(number.numerator * scale // number.denominator, scale)
    return f"{integral}.{remainder:0{places}d}"


if __name__ == "__main__":
    coefficient = spread_coefficient()
    # Independently computed by adding both disjoint orientations to C_S.
    assert coefficient == Fraction(
        87965011859590395559152098368077485014178420175365193522512487013280087205092755962553,
        2114954503179843945312500000000000000000000000000000000000000000000000000000000000000,
    )
    gap = 42 - coefficient
    print(f"Exact coefficient: {coefficient}")
    print(f"Coefficient rounded down to 12 decimal places: {rounded_down(coefficient, 12)}")
    print(f"Exact gap to 42: {gap}")
    print(f"Gap rounded down to 12 decimal places: {rounded_down(gap, 12)}")
