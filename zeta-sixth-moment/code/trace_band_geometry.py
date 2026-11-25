"""Rational mass comparison on 1 < r < 201/200, with r=k+z and k=x+y."""
from fractions import Fraction
from math import factorial

from marked_geometry import mass, reflected
from spread_geometry import spread_coefficient, rounded_down

eta = Fraction(1, 200)
ordered_band = [(1, 0, 0, 0), (-2, 1, 0, 0), (1, -1, 1, 0),
                (0, 0, -1, 1), (0, 1, 1, -1), (0, -200, -200, 201)]
box = [(20, 0, 0, -1), (-20, 0, 0, 3), (0, 0, 200, -99), (0, 0, -1000, 499)]
# At z < 1/2 and r > 1, every point is narrow and k > r/2 > 1/2.
# The old box and strip both require z > 1/2. Both reflected versions
# are absent in the lower band. The extra row enforces the new cut.
new_patch = [(-4, 0, 0, 1), (0, 0, -2, 1), (0, -61, -40, 51)]
# Extend past z=1/2 to k>z, explicitly excluding the old spread.
# Here z<201/400, whereas the old small box requires z>.53.
new_balanced = [(-4, 0, 0, 1), (0, 1, -1, 0), (2, 0, -2, 1), (0, -61, -40, 51)]
# For x >= 1/4 only the old triangle and direct cubic strip may be
# lost outside spread. Both have k < r/2. Bound their union by this cap.
old_cap = [(4, 0, 0, -1), (0, -1, 1, 0)]


def factorable_extra_mass(narrow_half):
    """Mass of the legacy thin factorable window (1/2<k<0.5000001, 8k/25<x<9k/25),
    both orientations, beyond the near-critical union. This window is from an
    earlier draft and is not the factorable region of the paper; see
    factorable_polygon_check.py for the factorable stage 41.6117... and
    mixed_row_checks.py for the release coefficient 41.6406...."""
    factorable = [(0, 2, 0, -1), (0, -10_000_000, 0, 5_000_001),
                  (25, -8, 0, 0), (-25, 9, 0, 0)]
    assert mass(narrow_half + [reflected(row) for row in factorable]) == 0
    return 2*mass(narrow_half + factorable + [(0, 28, 7, -18)])


if __name__ == "__main__":
    simple, enlarged, balanced, cap = [mass(ordered_band + cuts) for cuts in (box, new_patch, new_balanced, old_cap)]
    old_bound = factorial(9)*eta**5/128
    assert cap < old_bound < simple < enlarged < balanced
    net = 2*(balanced-cap)
    coefficient = spread_coefficient()+net
    for name, value in [('rectangular patch per band', simple), ('enlarged patch per band', enlarged),
                        ('balanced patch per band', balanced), ('old cap per band', cap), ('two-band net gain', net), ('coefficient', coefficient)]:
        print(name, value, rounded_down(value, 15))

    # Ideal short-slot, dominant and short-trace families miss exactly this
    # region. Its preimage under the half-pair-sum map provides a second check.
    omitted = [(-2, 1, 0, 0), (1, -1, 1, 0), (4, 0, 0, -1), (0, 0, -4, 3),
               (0, 1, 1, -1), (0, -1, -1, 2), (0, 1, -1, 0), (2, -1, -1, 1)]
    central_short_pair = [(1, 0, 0, 0), (-2, 1, 0, 0), (1, -1, 1, 0),
                          (0, 0, -1, 1), (0, 1, 1, -1), (0, -2, 0, 1)]
    pair_mass = mass(central_short_pair)
    omitted_mass = mass(omitted)
    assert pair_mass == Fraction(105, 8)
    assert omitted_mass == (40-2*pair_mass)/256 == Fraction(55, 1024)
    print('ideal omitted mass', omitted_mass, 'ideal ceiling', 42-omitted_mass)

    # On this wider band compare the entire replacement and old masses.
    # Narrow, k>=1/2 is the complement of spread and the old triangle.
    # Only the direct old strip meets this complement: the small old box
    # requires r>.53+.50000001>102/101; its reflection also misses the band.
    wider = ordered_band[:-1] + [(0, -101, -101, 102)]
    gap = wider + [(2, 0, -2, 1), (0, 2, 0, -1)]
    old_strip = [(0, -1, 1, 0), (0, 0, 50_000_000, -25_000_001), (0, -61, -40, 51)]
    old_mass = mass(wider) - mass(gap) + mass(gap + old_strip)
    replacement_mass = mass(wider + [(-4, 0, 0, 1), (0, -61, -40, 51)])
    wider_coefficient = spread_coefficient() + 2*(replacement_mass-old_mass)
    print('wider-band coefficient', wider_coefficient, rounded_down(wider_coefficient, 15))

    # Add every direct and reflected cubic profile from the generalized HB
    # comparison. Reflection has trace >3/2 on the lower central half, so
    # only direct HB can meet this half. The previous strip is a subset.
    # The old narrow box remains disjoint: its cost exceeds 51.7.
    lower_half = ordered_band[:-1] + [(0, -2, -2, 3)]
    narrow = lower_half + [(2, 0, -2, 1), (0, 2, 0, -1)]
    direct_hb = [(0, -61, -40, 51), (0, -1, 0, 1)]
    old_box = [(100, 0, 0, -17), (-1000, 0, 0, 171),
               (0, 100_000_000, 0, -50_000_001), (0, -50_000_000, 0, 25_000_001),
               (0, 0, 100, -53), (0, 0, -50, 27)]
    assert mass(narrow + direct_hb + old_box) == 0
    hb_coefficient = 42 - 2*(mass(narrow) - mass(narrow + direct_hb) - mass(narrow + old_box))
    assert hb_coefficient == spread_coefficient() + 2*(mass(narrow + direct_hb) - mass(narrow + old_strip))
    balanced_gain = 2*mass(omitted + lower_half + direct_hb)
    ideal_hb_ceiling = 42 - omitted_mass + balanced_gain
    for name, value in [('HB coefficient', hb_coefficient), ('HB gain on ideal blind set', balanced_gain),
                        ('ideal ceiling including HB', ideal_hb_ceiling)]:
        print(name, value, rounded_down(value, 15))

    # Full near-critical comparison contains the old strip, old box and HB
    # on the narrow gap, where k>=1/2. For HB, r<(51-21/2)/40=81/80
    # and 21k+7r<51-33r<18. Reflection exchanges the trace halves.
    critical = [(0, -14, -14, 15), (0, -28, -7, 18)]
    critical_mass = mass(narrow + critical)
    assert critical_mass == Fraction(2578241177999, 123966280704) - 21 + mass(narrow)
    for cell in [old_strip, old_box, direct_hb]:
        assert mass(narrow + cell) == mass(narrow + cell + critical)
    critical_coefficient = 42 - 2*(mass(narrow)-critical_mass)
    critical_balanced_gain = 2*mass(omitted + narrow + critical)
    critical_ceiling = 42 - omitted_mass + critical_balanced_gain
    assert critical_balanced_gain == Fraction(134173355669, 1470888975150000000)
    for name, value in [('critical coefficient', critical_coefficient),
                        ('critical gain on ideal blind set', critical_balanced_gain),
                        ('ideal ceiling including critical region', critical_ceiling)]:
        print(name, value, rounded_down(value, 15))

    factorable_gain = factorable_extra_mass(narrow)
    factorable_coefficient = critical_coefficient + factorable_gain
    print('legacy thin factorable window extra mass', factorable_gain)
    print('coefficient with the legacy thin factorable window (superseded)', factorable_coefficient,
          rounded_down(factorable_coefficient, 15))
    print('the factorable stage 41.6117... (factorable polygon of the paper) is checked in factorable_polygon_check.py;'
          ' the release coefficient 41.6406... in mixed_row_checks.py')
