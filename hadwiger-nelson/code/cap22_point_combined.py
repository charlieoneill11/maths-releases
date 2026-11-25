"""Integer box proof for adding two-circle forest edges to the capped unit forest."""

import argparse
from fractions import Fraction as F
import json
from math import ceil, isqrt, lcm
from pathlib import Path
from cap22_double_arcs import (
    SCALE,
    tiered_terms,
    short_pair_bounds,
    packing_geometry,
    weighted_geometry,
)

ROOT = Path(__file__).resolve().parent


class Bounds:
    def __init__(self, n, geometry_constants, star_credit):
        self.n = n
        self.g = g = geometry_constants
        self.p = ceil(SCALE * F(g['edge_probability']) - F(star_credit, 2))
        self.q = ceil(SCALE * F(g['blank']))
        # V bounds half the sum of squared degree deviations in a padded
        # critical graph. Its numerator is decreasing on the tested range.
        k = 2090
        quad = (
            F(-2, n),
            1 - F(24 * (n - 2) * (n - 3), (k - 2) * (k - 3)),
            n * (n - 1) + F(4 * 266 * n * (n - 1) * (n - 2) * (n - 3), 9 * k * (k - 1) * (k - 3)),
        )
        self.den = lcm(*(q.denominator for q in quad))
        self.a, self.b, self.c = [int(q * self.den) for q in quad]
        a, b, c = self.a, self.b, self.c
        self.max_edges = (isqrt(b * b - 4 * a * c) + b) // (-2 * a)
        assert (
            a < 0
            and b < 0
            and self.variance(self.max_edges) >= 0 > self.variance(self.max_edges + 1)
        )
        assert self.p > g['B'] and g['K'] == 0

    def variance(self, m):
        return (self.a * m + self.b) * m + self.c

    def upper(self, m, M, s, S, j, J):
        n = self.n
        g = self.g
        B = g['B']
        variance = self.variance(m)
        first = 2000 - g['first_retained_per_mille']

        def missed(second):
            maximum = first * S + second * J
            minimum = first * s + second * j
            norm = max(0, n * (first * first * S + second * second * J) - minimum * minimum)
            return (
                (2 * B * M * maximum + 2000 * n - 1) // (2000 * n)
                + 1
                + isqrt(2 * B * B * variance * norm // (self.den * n * 2000**2))
            )

        base = n * self.q + M * (self.p - B) - s * g['C'] - j * g['E']
        r_cost = min((n - s) * g['L'], (n - s) * g['T'] + J * g['U'], J * g['J'])
        upper = min(
            n * self.q + M * self.p,
            base + missed(1000 - g['second_retained_per_mille']) + r_cost,
            base + missed(2000 - g['second_retained_per_mille']),
        )
        if upper < SCALE:
            return upper
        off = min(S + J, n)
        min_off = s + j
        norm = max(0, n * off - min_off * min_off)
        degree_upper = (2 * M * off + n - 1) // n + 1 + isqrt(2 * variance * norm // (self.den * n))
        r_norm = max(0, n * S - s * s)
        r_degrees = (2 * M * S + n - 1) // n + 1 + isqrt(2 * variance * r_norm // (self.den * n))
        short_r, short_d = short_pair_bounds(S, J)
        r_short = min(r_degrees, short_r, (r_degrees + 5 * S + 1) // 2)
        d_short = min(degree_upper, short_d, (degree_upper + 5 * off + 1) // 2)
        return upper - tiered_terms(n, m, M, r_short, d_short, degree_upper, s + j, off)

    def check(self):
        n = self.n
        stack = [((0, self.max_edges), (0, n), (0, n))]
        boxes = maximum = 0
        while stack:
            (m, M), (s, S), (j, J) = stack.pop()
            boxes += 1
            if s + j > n:
                continue
            S, J = min(S, n - j), min(J, n - s)
            upper = self.upper(m, M, s, S, j, J)
            if upper < SCALE:
                maximum = max(upper, maximum)
                continue
            spans = [(m, M), (s, S), (j, J)]
            axis = max(range(3), key=lambda k: (spans[k][1] - spans[k][0]) * (1, 12, 12)[k])
            lo, hi = spans[axis]
            if lo == hi:
                return dict(
                    order=n, proved=False, examined=boxes, unresolved=[m, s, j], upper=upper
                )
            midpoint = (lo + hi) // 2
            for part in ((lo, midpoint), (midpoint + 1, hi)):
                child = spans.copy()
                child[axis] = part
                stack.append(child)
        return dict(
            order=n,
            proved=True,
            edge_ceiling=self.max_edges,
            examined=boxes,
            largest_upper_1e18=maximum,
        )


def check(orders):
    from cap22_point_crosscheck import audit

    g = json.loads((ROOT / 'cap22_point_parameters_result.json').read_text())
    source = json.loads((ROOT / 'cap22_partial_star_result.json').read_text())
    assert g['profile_sha256'] == source['profile_sha256']
    star = source['per_incidence_excess_picounits'] * (SCALE // 10**12)
    packing_geometry()
    angular = weighted_geometry(g)
    results = []
    for n in orders:
        if n < 2090:
            raise ValueError('the degree-variance sample requires at least 2090 points')
        primary = Bounds(n, g, star).check()
        independent = audit(n, g, star)
        assert primary['proved'] == independent['passed']
        results.append(dict(primary=primary, independent=independent))
    return dict(
        profile_sha256=g['profile_sha256'],
        credit_per_incidence_1e18=star,
        fine_angular_slack_1e18=angular['fine_minimum_medium_slack_1e18'],
        orders=results,
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('order', nargs='*', type=int, default=[10689, 10690])
    report = check(parser.parse_args().order)
    print(json.dumps(report, indent=2))
    # Exit with an error unless both programs certify the headline order
    # 10,689 when it is requested. Failures at other orders are only reported.
    for row in report['orders']:
        if row['primary']['order'] == 10689:
            assert row['primary']['proved'] and row['independent']['passed'], row
