"""Exact mass and geometry checks for the variable factorable-modulus windows."""

from dataclasses import dataclass
from fractions import Fraction as F
from math import factorial


BASE = F(2578241177999, 61983140352)
HALF = F(1, 2)


def lower_z(k):
    return (18 - 28 * k) / 7


def lower_x_from_shape(k):
    return lower_z(k) - HALF


@dataclass(frozen=True)
class Window:
    """The analytic interval lower*s < x/k < 1/2 - upper*s, s=2-1/k."""

    lower: F
    upper: F

    def lower_x(self, k):
        return self.lower * (2 * k - 1)

    def upper_x(self, k):
        return k / 2 - self.upper * (2 * k - 1)

    @property
    def switch(self):
        # Solve lower*(2k-1) = (18-28k)/7 - 1/2.
        return (29 + 14 * self.lower) / (56 + 28 * self.lower)

    @property
    def end(self):
        # The two analytic bounds touch at s=1/(2*(lower+upper)).
        return 1 / (2 - 1 / (2 * (self.lower + self.upper)))

    def cells(self):
        return ((HALF, self.switch, lower_x_from_shape),
                (self.switch, self.end, self.lower_x))


EARLIER = Window(F(218, 9), F(118, 9))
ENLARGED = Window(F(8), F(4))
FINAL = Window(F(7), F(7, 2))
WINDOWS = (EARLIER, ENLARGED, FINAL)


def check_geometry():
    assert (EARLIER.switch, EARLIER.end) == (F(3313, 6608), F(224, 445))
    assert (ENLARGED.switch, ENLARGED.end) == (F(141, 280), F(24, 47))
    assert 2 - 1 / ENLARGED.end == F(1, 24)
    assert (FINAL.switch, FINAL.end) == (F(127, 252), F(21, 41))
    assert 2 - 1 / FINAL.end == F(1, 21)

    for region in WINDOWS:
        assert region.lower_x(region.end) == region.upper_x(region.end)
        assert lower_x_from_shape(region.switch) == region.lower_x(region.switch)
        assert lower_x_from_shape(HALF) > region.lower_x(HALF)
        assert lower_x_from_shape(region.end) < region.lower_x(region.end)
        assert HALF < region.switch < region.end
        # The constraints are affine in (k,x,z). Checking each vertex
        # proves inclusion of the complete closed cell.
        for left, right, lower_x in region.cells():
            for k in (left, right):
                bottom, top = lower_x(k), region.upper_x(k)
                assert bottom <= top
                for x in (bottom, top):
                    assert x >= max(region.lower_x(k), lower_x_from_shape(k))
                    assert lower_z(k) <= HALF + x
                    for z in (lower_z(k), HALF + x):
                        assert 0 < x <= k - x < z < 1
                        assert 1 < k + z < F(3, 2)
                        assert z - x <= HALF
                        assert 21 * k + 7 * (k + z) >= 18

    # The enlarged analytic bounds contain the earlier ones for all k>=1/2.
    for smaller, larger in zip(WINDOWS, WINDOWS[1:]):
        assert larger.lower < smaller.lower and larger.upper < smaller.upper
        assert larger.end > smaller.end
    # The earlier polygon in turn contains the previous rectangular window.
    for k in (HALF, F(10009, 20000)):
        for x in (F(3, 20) * k, F(9, 20) * k):
            assert max(EARLIER.lower_x(k), lower_x_from_shape(k)) < x < EARLIER.upper_x(k)


# Closed Newton–Cotes with nine nodes, exact on degrees through nine.
# After substitution of the affine fiber endpoints the polynomial degrees
# in z, x, k are at most four, seven, eight, respectively.
NODES = [F(i, 8) for i in range(9)]
WEIGHTS = [F(v, 28350) for v in (989, 5888, -928, 10496, -4540, 10496, -928, 5888, 989)]


def integrate(function, lower, upper):
    width = upper - lower
    return width * sum(weight * function(lower + width * node)
                       for node, weight in zip(NODES, WEIGHTS))


def polygon_piece(left_k, right_k, lower_x, top_x):
    def at_k(k):
        def at_x(x):
            def density(z):
                return (k - 2 * x) ** 2 * (z - x) ** 2 * (z - k + x) ** 2
            return integrate(density, lower_z(k), HALF + x)
        return integrate(at_x, lower_x(k), top_x(k))
    return F(factorial(9), 2) * integrate(at_k, left_k, right_k)


def check_mass():
    for degree in range(10):
        assert sum(w * x ** degree for x, w in zip(NODES, WEIGHTS)) == F(1, degree + 1)
    initial = polygon_piece(HALF, F(50009, 100000), lambda k: 8 * k / 25, lambda k: 9 * k / 20)
    assert initial == F(459155484297833887104936937780339144819952075614485168333,
                        13398437500000000000000000000000000000000000000000000000000000)
    rectangle = polygon_piece(HALF, F(10009, 20000), lambda k: 3 * k / 20, lambda k: 9 * k / 20)
    assert rectangle == F(474972458475450714280513956751844313011900907,
                          1229312000000000000000000000000000000000000000000)
    earlier, enlarged, final = [
        sum(polygon_piece(left, right, bottom, region.upper_x)
            for left, right, bottom in region.cells())
        for region in WINDOWS
    ]
    assert earlier == F(13125748304209438056265098078647779763831539,
                        5651955025980035876577057005295558451200000000)
    assert enlarged == F(197809504776695813956171293, 24598305385293960241331200000)
    assert BASE + enlarged == F(3070155417138857932831680463879, 73794916155881880723993600000)
    assert final == F(144905581968317194975, 15466585661776021893456)
    assert initial < rectangle < earlier < enlarged < final
    coefficient = BASE + final
    assert coefficient == F(2941671429655121167078297, 70704391596690385798656)
    return coefficient


def check_smooth_regions():
    one_axis = Window(F(6), F(3))
    previous = BASE + sum(polygon_piece(a, b, bottom, one_axis.upper_x)
                          for a, b, bottom in one_axis.cells())
    assert previous == F(33010372229549007162589, 793384196505600000000)

    two_axes = Window(F(5), F(3, 2))
    assert two_axes.switch == F(99, 196) and two_axes.end == F(13, 25)
    assert 2 - 1 / two_axes.end == F(1, 13)
    # All faces are affine in k, x, z. Test the vertices of each cell.
    for left, right, bottom in two_axes.cells():
        for k in (left, right):
            top = two_axes.upper_x(k)
            assert bottom(k) == max(two_axes.lower_x(k), lower_x_from_shape(k))
            assert bottom(k) <= top
            for x in (bottom(k), top):
                assert lower_z(k) <= HALF + x
                for z in (lower_z(k), HALF + x):
                    assert 0 < x <= k - x < z < 1
                    assert 1 < k + z < F(3, 2) and z - x <= HALF
                    assert 21 * k + 7 * (k + z) >= 18

    increment = sum(polygon_piece(a, b, bottom, two_axes.upper_x)
                    for a, b, bottom in two_axes.cells())
    assert increment == F(840731426179152778718787, 52986177566328125000000000)
    coefficient = BASE + increment
    assert coefficient == F(3307268442615739142376085993, 79479266349492187500000000)
    assert previous < coefficient
    return coefficient


if __name__ == "__main__":
    check_geometry()
    check_mass()
    print("Polygon coefficient mu(U_6) (factorable stage):", check_smooth_regions())
