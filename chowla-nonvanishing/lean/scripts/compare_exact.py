#!/usr/bin/env python3
"""Compare the exploratory Lean evaluator with exact released-program values."""

import argparse
from fractions import Fraction
import importlib
from pathlib import Path
import random
import subprocess
import tempfile
from time import perf_counter

from import_rows import programs


LANDING = Path(__file__).resolve().parents[1]
SUITES = ("smoke", "208", "4287", "3000")


def serialize(value):
    q = Fraction(value)
    return f"{q.numerator}/{q.denominator}"


def load_oracles(release):
    rows, *_ = programs(release / "code")
    contraction = importlib.import_module("chowla_one_exception_certificate")
    partitions = importlib.import_module("chowla_octic_crosscheck")
    cubic, quartic = contraction.cubic, contraction.quart
    spectral = cubic.moments
    spline = cubic.splines
    center = spectral.integer_spline(spline.approximate_H())
    families = [
        rows["r0"],
        rows["r1Grid"] + rows["r1Modes"],
        *(rows[f"r{i}"] for i in range(2, 10)),
    ]

    def prepare(widths, coefficients, weight):
        p = spectral.integer_spline(spline.legendre_test(coefficients, 1 - sum(widths)))
        return (widths, p, sum(map(abs, coefficients))), weight

    groups = [[prepare(*row) for row in family] for family in families]
    groups.append([
        (((width,) if width else (), p, size), 1)
        for width, p, size in cubic.subgrid.linear
    ])

    def central(data):
        (widths, profile, size), weight = data
        if not widths:
            return "0/1 0/1"
        if len(widths) == 1:
            lo, hi = spectral.central_bounds(center, [(widths[0], profile, size)], [])
        else:
            lo, hi = quartic.central_enclosure(center, (widths, profile, size))
        weighted = (weight * lo, weight * hi) if weight >= 0 else (weight * hi, weight * lo)
        return " ".join(map(serialize, weighted))

    def expected(case, inner):
        if len(case) == 3:
            _, group, index = case
            return central(groups[group][index])
        a, i, b, j = case
        left, wl = groups[a][i]
        right, wr = groups[b][j]
        return serialize(wl * wr * inner(left, right))

    gram_methods = {
        "smoke": contraction.inner,
        "208": partitions.partition_inner,
        "4287": cubic.inner_product,
        "3000": partitions.partition_inner,
    }
    return groups, expected, gram_methods


def suite_cases(suite, data):
    def group_indices(indices):
        return [(g, i) for g in indices for i in range(len(data[g]))]

    if suite == "smoke":
        rng = random.Random(42)
        gram_cases = []
        for _ in range(80):
            a, b = rng.randrange(10), rng.randrange(10)
            gram_cases.append((a, rng.randrange(len(data[a])), b, rng.randrange(len(data[b]))))
        for g in range(10):
            i = len(data[g]) - 1
            gram_cases.append((g, i, g, i))
        central_cases = [
            ("C", g, i) for g in range(10) for i in sorted({0, len(data[g]) - 1})
        ]
        return gram_cases + central_cases
    if suite == "208":
        return [
            (7, i, b, j)
            for i in range(len(data[7]))
            for b, j in group_indices([6]) + [(7, j) for j in range(i + 1)]
        ]
    if suite == "4287":
        old = group_indices([10, 2, 3])
        return [
            (4, i, b, j)
            for i in range(len(data[4]))
            for b, j in old + [(4, j) for j in range(i + 1)]
        ]
    inherited = group_indices([10, 2, 3, 4, 5])
    added = group_indices([8, 9])
    sample = random.Random(20261124).sample(range(len(added) * len(inherited)), 3000)
    return [
        (*added[i // len(inherited)], *inherited[i % len(inherited)])
        for i in sample
    ]


def run_suite(suite, data, expected, method):
    cases = suite_cases(suite, data)
    start = perf_counter()
    oracle = [expected(case, method) for case in cases]
    oracle_time = perf_counter() - start

    with tempfile.TemporaryDirectory(prefix="chowla-regression-") as temp:
        queries = Path(temp) / "queries.txt"
        queries.write_text("".join(" ".join(map(str, row)) + "\n" for row in cases))
        start = perf_counter()
        output = subprocess.run(
            ["lake", "env", "lean", "--run", "Chowla/CheckerRegression.lean", str(queries)],
            check=True,
            cwd=LANDING,
            stdout=subprocess.PIPE,
            text=True,
        )
    lean_time = perf_counter() - start
    actual = output.stdout.splitlines()
    if len(actual) != len(cases):
        raise SystemExit(f"{suite}: Lean returned {len(actual)} answers for {len(cases)} queries")
    discrepancies = [
        (case, want, got)
        for case, want, got in zip(cases, oracle, actual, strict=True)
        if want != got
    ]
    for case, want, got in discrepancies:
        print(f"{suite}, {case}: program {want}; Lean {got}")
    ncentral = sum(len(case) == 3 for case in cases)
    print(
        f"{suite}: {len(cases) - ncentral} Gram values, {ncentral} central enclosures, "
        f"{len(discrepancies)} differences, Lean {lean_time:.3f}s, oracle {oracle_time:.3f}s",
        flush=True,
    )
    if discrepancies:
        raise SystemExit(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path, help="chowla-nonvanishing directory of the release")
    parser.add_argument("--suite", choices=(*SUITES, "all"), default="smoke")
    args = parser.parse_args()
    data, expected, methods = load_oracles(args.release.resolve())
    for suite in SUITES if args.suite == "all" else (args.suite,):
        run_suite(suite, data, expected, methods[suite])


if __name__ == "__main__":
    main()
