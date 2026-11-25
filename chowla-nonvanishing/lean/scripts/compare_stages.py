#!/usr/bin/env python3
"""Compare the reported Lean stage bounds with exact outputs from the release."""

import argparse
from fractions import Fraction
import importlib
from itertools import chain
from multiprocessing import Pool
from pathlib import Path
import subprocess
import sys
from time import perf_counter


PROJECT = Path(__file__).resolve().parents[1]
P0 = (19 - Fraction("3.916317365")) / 16


def capture(call, visit, args=()):
    """Observe one released function's local variables without changing its arithmetic."""
    def tracer(frame, event, _arg):
        if event == "call" and frame.f_code is call.__code__:
            return visit
        return None

    old = sys.gettrace()
    sys.settrace(tracer)
    try:
        return call(*args)
    finally:
        sys.settrace(old)


def early_oracles(jobs):
    cubic = importlib.import_module("chowla_cubic_single_certificate")
    quartic = importlib.import_module("chowla_quartic_single_certificate")
    quintic = importlib.import_module("chowla_one_exception_certificate")
    subgrid = cubic.subgrid
    center = subgrid.moments.integer_spline(subgrid.spline.approximate_H())
    first_lo, upper = subgrid.moments.central_bounds(center, subgrid.linear, subgrid.pairs)
    with Pool(jobs) as workers:
        costs = workers.map(subgrid.linear_norm_row, range(len(subgrid.linear)))
        costs += workers.map(subgrid.quadratic_norm_row, range(len(subgrid.pairs)))
    gram = Fraction(sum(costs), subgrid.ROUNDING_SCALE)
    yield (first_lo, upper, gram, P0 + first_lo**2 / (2 * gram))

    batches = (
        (cubic.certify, cubic.CUBIC_ROWS, "norm_upper"),
        (quartic.certify, [((width,) * 4, coeffs) for width, coeffs in quartic.QUARTIC_ROWS],
         "norm_upper"),
        (quintic.certify, quintic.QUINTIC_ROWS, "norm"),
    )
    for run, new_rows, gram_name in batches:
        for widths, coeffs in new_rows:
            upper += quartic.central_enclosure(center, quartic.profile_row(widths, coeffs))[1]
        output = {}

        def visit(frame, event, _arg):
            frame.f_trace_lines = False
            if event == "return":
                output.update(frame.f_locals)
            return visit

        gain = capture(run, visit)
        yield (output["lower"], upper, output[gram_name], gain)


def late_oracles():
    sextic = importlib.import_module("chowla_sextic_septic_certificate")
    octic = importlib.import_module("chowla_octic_certificate")
    triple = importlib.import_module("chowla_three_width_certificate")
    yield (sextic.certify(),)

    totals = {}
    stops = {22, 125, 151}

    def visit(frame, event, _arg):
        if event == "line" and "bound" in frame.f_locals:
            count = len(frame.f_locals["fitted_rows"])
            if count in stops:
                totals.setdefault(count, frame.f_locals["bound"])
        return visit

    # The triple program runs the octic function over the full ordered list.
    old = octic.certify
    octic.certify = lambda *args: capture(old, visit, args)
    try:
        triple.certify()
    finally:
        octic.certify = old
    yield from ((totals[stop],) for stop in sorted(stops))


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path, help="Path to the released chowla-nonvanishing directory")
    parser.add_argument("--jobs", default=4, type=int, help="Stage-one oracle worker count")
    args = parser.parse_args()
    sys.path.insert(0, str(args.release.resolve() / "code"))
    records = subprocess.check_output(
        ["lake", "env", "lean", "--run", "scripts/reported_stages.lean"],
        cwd=PROJECT, text=True,
    )
    lean = [tuple(map(Fraction, row.split())) for row in records.splitlines()]
    started = perf_counter()
    for i, (want, actual) in enumerate(zip(chain(early_oracles(args.jobs), late_oracles()),
                                           lean, strict=True), 1):
        for field, x, y in zip(
            ("C⁻", "C⁺", "D⁺", "proportion") if i <= 4 else ("R",), actual, want, strict=True
        ):
            if x != y:
                raise SystemExit(f"Stage {i} {field} differs\nLean {x}\nPython {y}")
        finished = perf_counter()
        print(f"Stage {i} agrees on {len(want)} exact values ({finished - started:.3f} s)", flush=True)
        started = finished


if __name__ == "__main__":
    main()
