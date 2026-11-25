"""Circle-subdivision counts and blank-forest credits, using rational arithmetic."""

from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import json
from math import ceil, floor, isqrt
from pathlib import Path

from refit_wave_check import Hole, S

ROOT = Path(__file__).resolve().parent
PI_HI = F(355, 113)
DELTA = F(1837, 250000)
CUTOFF = F(22, 100)
UNIT_CONE = F(73, 10000)
SCALE = 10**18
PAIR_CREDIT = 2_800_000_000


@lru_cache(None)
def sampling(n, k=1317):
    assert n >= k >= 4
    p2 = F(k * (k - 1), n * (n - 1))
    p4 = p2 * F((k - 2) * (k - 3), (n - 2) * (n - 3))
    return p2, p4, F(266 * (k - 2), 9)


def simple_edge_upper(n, m_low, m_high):
    p2, p4, intercept = sampling(n)
    # Above n/4 the Jensen bound decreases throughout the edge interval.
    linear_term = m_low if 4 * m_low >= n else m_high
    crossings = n * (n - 1) + linear_term - F(2 * m_low**2, n)
    return floor((crossings * p4 + intercept) / (6 * p2))


def clean_pair_lower(n, m_low, m_high, off_degree_upper):
    """Number with all four vertices in D, two minor gaps, chord at most .22."""
    assert 0 <= m_low <= m_high and off_degree_upper >= 0
    doubled = 2 * m_low - simple_edge_upper(n, m_low, m_high)
    excess = PI_HI * n - (m_low - off_degree_upper) * DELTA
    return max(0, ceil(doubled - 2 * off_degree_upper - excess / (CUTOFF - DELTA)))


def geometry(g):
    path = ROOT / "cap16_finite_wave.json"
    assert sha256(path.read_bytes()).hexdigest() == g["profile_sha256"]
    assert 2 * F(g["d"]) == DELTA
    hole = Hole(json.loads(path.read_text()))
    cell_area = F(hole.x, S)
    # Medium chord. Displacement after subtracting (0,2) is at most
    # (2t, .01214+t^2). Vertical lies strictly inside the minor gap.
    angle = F(".0024")
    deficit = F(".01214")
    assert (2 - deficit) ** 2 <= 4 - CUTOFF**2
    assert angle + UNIT_CONE < F(".02") / 2
    bins = 16
    step = angle / bins
    medium = sum(
        hole.overlap(2 * t, deficit + t * t) for t in (step * i for i in range(1, bins + 1))
    )
    medium *= 2 * step / PI_HI

    # Small chord. Condition on a rectangle for the center midpoint.
    angle = F(".00085")
    half_x, y0, y1 = F(".00075"), F(".003"), F(".0046")
    sag = F(".0000505")
    assert (1 - sag) ** 2 <= 1 - F(".02") ** 2 / 4
    yshift = sag + angle**2 / 2
    tailshift = yshift + UNIT_CONE**2 / 2
    assert y1 + yshift < F(".004651")
    assert y0 - tailshift > F(".00292")
    assert F(hole._width(4651000000), S) > half_x + angle
    width_upper = F(hole._width(2920000000) + 1, S)
    assert width_upper < F(".0027")
    assert width_upper + half_x + tailshift * angle < DELTA / 2
    # A putative blank tail is in the middle hole, using the lattice column
    # spacing 2x, row spacing 1/2, circumrectangle and these coordinate bounds.
    max_width = F(max(hole.w), S)
    max_height = F(max(hole.y), S)
    assert half_x + angle + UNIT_CONE + max_width < 2 * cell_area
    assert y1 + tailshift + max_height < F(1, 2)
    assert angle < DELTA / 2 and angle + UNIT_CONE < 1
    small = 2 * angle / PI_HI * 4 * half_x * (y1 - y0) / cell_area
    assert min(small, medium) * SCALE >= PAIR_CREDIT
    return dict(
        small_chord_lower_1e18=floor(small * SCALE),
        medium_chord_lower_1e18=floor(medium * SCALE),
        uniform_lower_1e18=PAIR_CREDIT,
        profile_sha256=g["profile_sha256"],
    )


# Affine lower bound in units of 10^-18, per pair and per radian.
INTERCEPT = 23_000_000_000
ANGLE_COST = 98_000_000_000
R_DELTA = F(53, 10_000)
R_INTERCEPT = 7_900_000_000
FINE_INTERCEPT = 25_900_000_000
FINE_R_INTERCEPT = 9_300_000_000
FINE_ANGLE_COST = 110_000_000_000


def weighted_credit_lower(n, m_low, m_high, off_degree_upper):
    """Guaranteed total admissible credit, in 10^-18 units."""
    simple = simple_edge_upper(n, m_low, m_high)
    clean = max(0, 2 * m_low - simple - 2 * off_degree_upper)
    excess = PI_HI * n - (m_low - off_degree_upper) * DELTA
    return max(0, floor(clean * INTERCEPT - ANGLE_COST * excess))


def tiered_credit_lower(n, m_low, m_high, off_r_degree_upper, off_d_degree_upper):
    """Two endpoint-separation tiers, requiring only the upper center in D."""
    return tiered_terms(
        n, m_low, m_high, off_r_degree_upper, off_d_degree_upper, off_d_degree_upper
    )


def short_pair_bounds(s, j):
    """Maximum pairs with chord below separation threshold of R, then D."""
    both_outside = s * (s - 1) // 2
    return 5 * s + both_outside, 14 * s + 8 * j + both_outside


def packed_credit_lower(n, m_low, m_high, s_max, j_max, off_d_degree_upper):
    """Only short chords spend endpoint exceptions. Degree loss is at heads."""
    short_r, short_d = short_pair_bounds(s_max, j_max)
    return tiered_terms(n, m_low, m_high, short_r, short_d, off_d_degree_upper)


def tiered_terms(
    n, m_low, m_high, short_r, short_d, head_degree, head_count_lower=0, head_count_upper=None
):
    """Endpoint exceptions and center degree are upper bounds, root omissions a lower."""
    doubled = 2 * m_low - simple_edge_upper(n, m_low, m_high)
    half_center_loss = F(head_degree, 2)
    r_pairs = max(0, doubled - short_r - half_center_loss)
    d_pairs = max(0, doubled - short_d - half_center_loss)
    mandatory = (m_low - short_r) * R_DELTA + (m_low - short_d) * (DELTA - R_DELTA)
    excess = PI_HI * n - mandatory
    # Each oriented eligible pair uses only its upper circle's gap. On
    # D-centered circles there are at least 2m-L total arcs; the rest
    # of the vertex circles contribute no angle to this budget.
    centered_excess = PI_HI * (n - head_count_lower) - mandatory + DELTA * half_center_loss
    excess = min(excess, centered_excess)
    coarse = R_INTERCEPT * r_pairs + (INTERCEPT - R_INTERCEPT) * d_pairs - ANGLE_COST * excess
    fine = (
        FINE_R_INTERCEPT * r_pairs
        + (FINE_INTERCEPT - FINE_R_INTERCEPT) * d_pairs
        - FINE_ANGLE_COST * excess
    )
    if head_count_upper is not None:
        h = head_count_upper
        # Undoubled arcs use angle but never give a long blank-forest edge.
        # Integrate lower bounds for their length in excess of DELTA.
        extra_all = extra_centered = 0
        last_tenth = 10
        for tenths in (14, 19, 24, 29, 34, 39, 44):
            disk_limit = (10 + 2 * tenths) ** 2 // 100
            dd = (disk_limit - 1) * (n - head_count_lower) // 2
            other = min(2 * head_degree, disk_limit * h + h * (h - 1) // 2)
            singles = 2 * m_low - 2 * doubled - dd - other
            extra_all += (tenths - last_tenth) * max(0, singles)
            extra_centered += (tenths - last_tenth) * max(0, singles - head_degree)
            last_tenth = tenths
        spare = min(
            PI_HI * n - mandatory - DELTA * extra_all / 20,
            centered_excess - DELTA * extra_centered / 20,
        )
        # Use the affine pair counts without clipping for this alternative.
        # Their total slope as a function of actual doubled count is I.
        # The new reserve can decrease at rate at most tau_max-DELTA.
        for high, low, slope in (
            (INTERCEPT, R_INTERCEPT, ANGLE_COST),
            (FINE_INTERCEPT, FINE_R_INTERCEPT, FINE_ANGLE_COST),
        ):
            assert high > slope * DELTA * (last_tenth - 10) / 10
            linear = high * (doubled - half_center_loss) - low * short_r - (high - low) * short_d
            fine = max(fine, linear - slope * spare)
    return max(0, floor(max(coarse, fine)))


def packing_geometry():
    # Within R, neighbors of an R point have radii in [R_DELTA, DELTA].
    # If nine lay within DELTA, two would subtend angle <=2pi/9.
    # For that angle squared distance is convex in each radius, so the
    # four radial corners suffice to exclude this pair.
    theta = 2 * PI_HI / 9
    assert (
        max((a - b) ** 2 + a * b * theta**2 for a in (R_DELTA, DELTA) for b in (R_DELTA, DELTA))
        < R_DELTA**2
    )
    # Around any point use area of disjoint R_DELTA/2 disks.
    assert floor((1 + 2 * DELTA / R_DELTA) ** 2) == 14
    # Around a point outside R and within R_DELTA, six R neighbors would
    # give two at angular difference <=pi/3. Their separation is at
    # most R_DELTA by separate convexity and cos(pi/3)=1/2.
    assert max(a * a + b * b - a * b for a in (0, R_DELTA) for b in (0, R_DELTA)) == R_DELTA**2


def center_distance_deficit(chord):
    # Upper bound 2-sqrt(4-chord^2) with 10^-8 length resolution.
    return 2 - F(isqrt(floor((4 - chord**2) * 10**16)), 10**8)


def sliced_midpoint(hole, separation=DELTA, chord_upper=F(".02"), angle_bins=32, height_bins=48):
    # Uniform over chords in (delta, .02]. Each box of (angle, |M_y|)
    # guarantees a strip of M_x yielding blank centers and no blank unit tail.
    end = min(F(".00365"), separation / 2)
    dt, dy = end / angle_bins, F(".009") / height_bins
    assert end <= separation / 2
    sag = center_distance_deficit(chord_upper) / 2
    top = F(max(hole.y), S)

    def width(z, upper):
        # Round the argument down for an upper width and up for a lower
        # width, since widths are decreasing above the origin.
        scaled = floor(z * S) if upper else ceil(z * S)
        if scaled >= max(hole.y):
            return F(0)
        return F(hole._width(scaled) + int(upper), S)

    area = F(0)
    for j in range(1, angle_bins + 1):
        theta = j * dt
        center_y_shift = sag + theta**2 / 2
        tail_y_shift = center_y_shift + UNIT_CONE**2 / 2
        for i in range(height_bins):
            y = i * dy
            centers = width(y + dy + center_y_shift, False) - theta
            competitor = width(max(0, y - tail_y_shift), True)
            exclusion = separation / 2 - competitor - tail_y_shift * theta
            area += max(0, min(centers, exclusion))
    cell = F(hole.x, S)
    # Within all rectangles, any ordinary incoming blank tail lies
    # in the middle hole because the others are too far in x or y.
    halfwidth = F(max(hole.w), S)
    assert 2 * halfwidth + end + UNIT_CONE < 2 * cell
    assert F(".009") + tail_y_shift + top < F(1, 2)
    # Factors are 2/pi for the absolute polar angle and 2 each for
    # the signs of the two midpoint coordinates.
    return 8 * dt * dy * area / (PI_HI * cell)


def weighted_geometry(g):
    path = ROOT / "cap16_finite_wave.json"
    assert sha256(path.read_bytes()).hexdigest() == g["profile_sha256"]
    hole = Hole(json.loads(path.read_text()))
    small = sliced_midpoint(hole)
    r_small = sliced_midpoint(hole, R_DELTA)
    assert 2 * F(g["a"]) == R_DELTA
    assert r_small * SCALE > R_INTERCEPT
    # Away from the small chords, a successful absolute-angle interval
    # for class D also dominates the R affine bound at the same chord.
    assert INTERCEPT + ANGLE_COST * DELTA > R_INTERCEPT + ANGLE_COST * R_DELTA
    # Lower center distance from its D root is at most 2a+2d.
    assert F("1.9") * (1 - F(".00365") ** 2 / 2) > R_DELTA + DELTA
    assert F("1.9") ** 2 < 4 - F(".245") ** 2
    assert small * SCALE > INTERCEPT
    cuts = [F(i, 100) for i in (2, 4, 8, 12, 16, 18)]
    cuts += [F(i, 1000) for i in range(190, 246)]
    fine_small = min(
        sliced_midpoint(hole, lo, hi, 100, 180)
        for lo, hi in ((DELTA, F(".008")), (F(".008"), F(".02")))
    )
    fine_r_small = min(
        sliced_midpoint(hole, lo, hi, 100, 180)
        for lo, hi in ((R_DELTA, F(".006")), (F(".006"), F(".02")))
    )
    assert fine_small * SCALE > FINE_INTERCEPT and fine_r_small * SCALE > FINE_R_INTERCEPT
    assert FINE_INTERCEPT + FINE_ANGLE_COST * DELTA > FINE_R_INTERCEPT + FINE_ANGLE_COST * R_DELTA
    margins, fine_margins = [], []
    for lo, hi in zip(cuts, cuts[1:]):
        deficit = center_distance_deficit(hi)
        angle = min(F(".0036"), lo / 2 - UNIT_CONE)
        assert angle > 0
        for steps, intercept, cost, output in (
            (48, INTERCEPT, ANGLE_COST, margins),
            (256, FINE_INTERCEPT, FINE_ANGLE_COST, fine_margins),
        ):
            step = angle / steps
            credit = sum(
                hole.overlap(2 * t, deficit + t * t)
                for t in (step * j for j in range(1, steps + 1))
            )
            credit *= 2 * step / PI_HI
            required = intercept - cost * (lo - DELTA)
            output.append(floor(credit * SCALE - required))
    assert min(margins + fine_margins) >= 0
    assert FINE_INTERCEPT - FINE_ANGLE_COST * (cuts[-1] - DELTA) <= 0
    assert INTERCEPT - ANGLE_COST * (cuts[-1] - DELTA) <= 0
    return dict(
        small_chord_lower_1e18=floor(small * SCALE),
        r_small_chord_lower_1e18=floor(r_small * SCALE),
        r_intercept_1e18=R_INTERCEPT,
        fine_small_chord_lower_1e18=floor(fine_small * SCALE),
        fine_r_small_chord_lower_1e18=floor(fine_r_small * SCALE),
        fine_minimum_medium_slack_1e18=min(fine_margins),
        fine_intercept_1e18=FINE_INTERCEPT,
        fine_r_intercept_1e18=FINE_R_INTERCEPT,
        fine_per_radian_1e18=FINE_ANGLE_COST,
        minimum_medium_slack_1e18=min(margins),
        medium_intervals=len(margins),
        intercept_1e18=INTERCEPT,
        per_radian_1e18=ANGLE_COST,
    )


def variance(n, m, k=2090):
    slope = F(24 * (n - 2) * (n - 3), (k - 2) * (k - 3))
    const = F(4 * 266 * n * (n - 1) * (n - 2) * (n - 3), 9 * k * (k - 1) * (k - 3))
    return n * (n - 1) + const + m * (1 - slope) - F(2 * m * m, n)


def check():
    g = json.loads((ROOT / "cap22_point_parameters_result.json").read_text())
    result = geometry(g)
    packing_geometry()
    n, cap = 10681, 402666
    assert variance(n, cap) >= 0 > variance(n, cap + 1)
    q = ceil(F(g["blank"]) * SCALE)
    p = ceil(F(g["edge_probability"]) * SCALE)
    net = p - g["B"]
    assert net > 0
    last_safe = (SCALE - 1 - n * q) // net
    largest = n * q + last_safe * net
    for m in range(last_safe + 1, cap + 1):
        score = n * q + m * net - PAIR_CREDIT * clean_pair_lower(n, m, m, 0)
        largest = max(largest, score)
    assert largest < SCALE and n * q + cap * net >= SCALE
    # Sample with 20 omitted centers and degree sum 2,000. Knowing their
    # number improves the angular bound by 20*pi - 1,000*delta.
    uncentered = tiered_terms(n, cap, cap, 100, 300, 2000)
    centered = tiered_terms(n, cap, cap, 100, 300, 2000, 20)
    assert centered - uncentered >= floor(ANGLE_COST * (20 * PI_HI - 1000 * DELTA)) > 0
    return dict(
        geometry=result,
        weighted_geometry=weighted_geometry(g),
        n=n,
        edge_ceiling=cap,
        no_discards=True,
        center_budget_test=dict(
            head_count=20, head_degree=2000, earned_extra_1e18=centered - uncentered
        ),
        last_safe_without_bonus=last_safe,
        maximum_score_upper_1e18=largest,
        at_ceiling=dict(
            simple_edges_upper=simple_edge_upper(n, cap, cap),
            doubled_lower=2 * cap - simple_edge_upper(n, cap, cap),
            weighted_credit_lower_1e18=weighted_credit_lower(n, cap, cap, 0),
            packed_weighted_credit_lower_1e18=packed_credit_lower(n, cap, cap, 0, 0, 0),
            clean_short_chord_lower=clean_pair_lower(n, cap, cap, 0),
            original_score_upper_1e18=n * q + cap * net,
            corrected_score_upper_1e18=n * q
            + cap * net
            - PAIR_CREDIT * clean_pair_lower(n, cap, cap, 0),
        ),
    )


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
