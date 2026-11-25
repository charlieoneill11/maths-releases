"""A degree-uniform locked-star improvement for the full six-label wave."""

from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path
from flint import acb, arb, ctx, fmpq

from cap22_finite_edge import check

ctx.prec = 100
S = 10**12
H = S // 2
N = 2**17
p = json.loads(Path(__file__).with_name('cap22_finite_edge_profile.json').read_text())
R = [width for _, width in p['right']]
step = H // (len(R) - 1)
U = 2 * p['x']
maxR = max(R)
assert all(R[j] <= R[j + 1] for j in range((len(R) - 1) // 2))


def bounds(y):
    """Outward integral bounds on the piecewise-affine right wall."""
    i, rem = divmod(y, step)
    if not rem:
        return R[i], R[i]
    numerator = R[i] * step + rem * (R[i + 1] - R[i])
    return numerator // step, -(-numerator // step)


@lru_cache(None)
def ray(q, k):
    x, y, den = N * N - k * k, 2 * N * k, N * N + k * k
    a, b = ((x, y), (-y, x), (-x, -y), (y, -x))[q]
    return a * S // den, -(-a * S // den), b * S // den, -(-b * S // den)


def statuses(box, color):
    """Return 0 for outside, 2 for inside up to seams, and 1 otherwise."""
    x, X, y, Y = box
    possible = False
    assert -2 * S <= x <= X <= 2 * S and 3 * U - maxR > 2 * S
    for m in range(-2, 3):
        if color <= 3:
            lo, hi = x - m * U, X - m * U
        else:
            lo, hi = m * U - X, m * U - x
        if hi <= 0 or lo >= maxR:
            continue
        low, high = y - 3 * m * H // 2, Y - 3 * m * H // 2
        for j in range(low // H, high // H + 1):
            if 1 + 3 * (color > 3) + (-j) % 3 != color:
                continue
            yl = min(H, max(0, low - j * H))
            yr = min(H, max(0, high - j * H))
            if yr <= yl:
                continue
            a, b = bounds(yl)
            e, f = bounds(yr)
            if low >= j * H and high <= (j + 1) * H and lo >= 0 and hi <= min(a, e):
                return 2
            top = maxR if yl <= H // 2 <= yr else max(b, f)
            if lo < top:
                possible = True
    return int(possible)


def runs(box, alternate):
    """Common angular step-function envelope for every source in the box."""
    x, X, y, Y = box
    spans = []
    for q in range(4):

        def visit(a, b):
            left, right = ray(q, a), ray(q, b)
            target = (
                x + min(left[0], right[0]),
                X + max(left[1], right[1]),
                y + min(left[2], right[2]),
                Y + max(left[3], right[3]),
            )
            native = statuses(target, 1)
            other = statuses(target, alternate)
            if native == 2:
                coefficient = (2, 0)
            elif other == 2:
                coefficient = (-2, 0)
            elif native == other == 0:
                coefficient = (0, 0)
            elif b > a + 1:
                mid = (a + b) // 2
                visit(a, mid)
                visit(mid, b)
                return
            else:
                coefficient = (int(native > 0) - int(other > 0), int(native > 0) + int(other > 0))
            if spans and spans[-1][:2] == [q, coefficient] and spans[-1][3] == a:
                spans[-1][3] = b
            else:
                spans.append([q, coefficient, a, b])

        visit(0, N)
    return spans


@lru_cache(None)
def angular(q, k):
    return arb.pi() * q / 2 + 2 * arb(fmpq(k, N)).atan()


def spectrum(box, alternate, K):
    known, error = arb(0), arb(0)
    harmonics = [acb(0) for _ in range(K)]
    for q, (coefficient, radius), a, b in runs(box, alternate):
        if not (coefficient or radius):
            continue
        low, high = angular(q, a), angular(q, b)
        known += coefficient * (high - low)
        error += radius * (high - low)
        if coefficient:
            start, end = acb(0, low).exp(), acb(0, high).exp()
            s = t = acb(1)
            for k in range(K):
                s, t = s * start, t * end
                harmonics[k] += coefficient * (s - t) / (k + 1)
    # Both coefficient and radius are twice their actual values. A
    # common unit complex factor in the nonzero moments is immaterial.
    norm = 4 * arb.pi()

    def lower(z):
        return int((z.lower() * QUANT).floor().unique_fmpz())

    return (
        lower((known - error) / norm),
        [max(0, lower((abs(h) - error) / norm)) for h in harmonics],
    )


QUANT = 10**10
FREQUENCIES = 56
THRESHOLDS = 10**5
TARGET = F(8, 10**9)
MICRO = 10**6  # scaled integer coordinates per millionth of a unit


def source_rectangles():
    # Disjoint parts of one positive master tile, below its midheight.
    for y in range(0, 6000, 20):
        for a, b in [(0, 5), (5, 15), (15, 35), (35, 65)]:
            yield (a, b, y, y + 20), 4
    for x in [*range(80, 6000, 20), *range(866000, 876400, 20)]:
        for a, b in [(0, 5), (5, 15), (15, 35), (35, 65)]:
            yield (x, x + 20, a, b), 2
    for y in range(0, 250000, 100):
        r = bounds(y * MICRO)[0] // MICRO
        for a, b in [(0, 10), (10, 30), (30, 60), (60, 95)]:
            yield (r - b, r - a, y, y + 100), 6


def source_data():
    result = []
    for (a, b, c, d), alternate in source_rectangles():
        box = tuple(z * MICRO for z in (a, b, c, d))
        assert statuses(box, 1) == 2 and 0 <= c < d <= 250000
        if alternate == 4:
            assert 0 <= a < b <= 65
        elif alternate == 2:
            assert 80 <= a < b <= 876400
        else:
            assert 876400 < a < b
        mean, moments = spectrum(box, alternate, FREQUENCIES)
        outside_high_test = a >= 600 or c >= 1050
        result.append(((b - a) * (d - c), mean, moments, outside_high_test))
    return result


def saturated_boxes():
    # Arc fraction guaranteed to have the source's native label. Used on
    # the whole square even if there are other (uncertified) native angles.
    probabilities = []
    for y in range(0, 1050, 50):
        for x in range(0, 600, 50):
            box = tuple(z * MICRO for z in (x, x + 50, y, y + 50))
            assert statuses(box, 1) == 2
            width = sum(
                (angular(q, b) - angular(q, a) for q, (v, _), a, b in runs(box, 4) if v == 2),
                arb(0),
            )
            lower = (width / (2 * arb.pi())).lower()
            probabilities.append(int((lower * QUANT).floor().unique_fmpz()))
    return probabilities


def large_degree(probabilities, degree):
    # Each box and its reflection in y=H/2 occurs once per native-tile
    # mean area xH. The integrand is the excess per incidence, f-1/d.
    positive = sum(max(0, F(v, QUANT) - F(1, degree)) for v in probabilities)
    return 4 * 2500 * positive / p['x']


def power_certificate(rows, degree, target):
    # If |power_sum(k)|/degree >= threshold(k), integrated positive
    # star-count excess on these boxes is already at least target.
    thresholds = []
    for k in range(FREQUENCIES):
        column = [(a, mu * THRESHOLDS, h[k]) for a, mu, h, _ in rows]

        def enough(t):
            val = sum(a * max(0, mu + t * h) for a, mu, h in column)
            return 2 * val * target.denominator >= target.numerator * p['x'] * QUANT * THRESHOLDS

        if not enough(THRESHOLDS):
            # No useful constraint from this coefficient. All power sums
            # are at most the degree by the triangle inequality.
            thresholds.append(THRESHOLDS)
            continue
        low, high = 0, THRESHOLDS
        while high - low > 1:
            mid = (low + high) // 2
            if enough(mid):
                high = mid
            else:
                low = mid
        thresholds.append(high)
    n = len(thresholds)
    upper = sum(F(2 * (n - k), n + 1) * F(t, THRESHOLDS) ** 2 for k, t in enumerate(thresholds))
    required = F(n + 1, degree) - 1
    assert upper < required, (degree, float(upper), float(required))
    return dict(
        degree_up_to=degree,
        harmonic_target=str(target),
        fejer_upper=str(upper),
        fejer_required=str(required),
        threshold_denominator=THRESHOLDS,
        thresholds=thresholds,
    )


def run():
    baseline = check(p)
    rows = source_data()
    probabilities = saturated_boxes()
    proofs = [power_certificate(rows, 23, TARGET)]
    separate = [r for r in rows if r[3]]
    for degree in range(24, 28):
        high = large_degree(probabilities, degree)
        if high < TARGET:
            proofs.append(power_certificate(separate, degree, TARGET - high))
    assert large_degree(probabilities, 28) > TARGET
    effective = F(baseline['edge_probability_upper']) - TARGET / 2
    m = (effective.denominator - 1) // effective.numerator
    return dict(
        wave_upper=baseline['edge_probability_upper'],
        wave_edges=baseline['edges'],
        source_boxes=len(rows),
        source_boxes_outside_high_rectangle=len(separate),
        angular_resolution_per_quadrant=N,
        certified_excess_per_incidence=str(TARGET),
        large_degree_excess={str(d): str(large_degree(probabilities, d)) for d in range(24, 29)},
        power_certificates=proofs,
        effective_bound=str(effective),
        edges=m,
    )


if __name__ == '__main__':
    report = run()
    print(json.dumps(report, indent=2))
    # Theorem 2 claims every graph with at most 245,510 edges.
    assert report['edges'] >= 245510, report['edges']
