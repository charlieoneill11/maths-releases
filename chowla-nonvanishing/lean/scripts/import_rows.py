#!/usr/bin/env python3
"""Import the released certificate's exact rows and separately transcribe its TeX tables."""

import argparse
import importlib
import re
import sys
from fractions import Fraction
from pathlib import Path


MODULE_DIR = Path(__file__).resolve().parents[1] / "Chowla"


def row(widths, coefficients, width_denominator=160, weight=1):
    return (
        tuple(Fraction(width, width_denominator) for width in widths),
        tuple(map(Fraction, coefficients)),
        Fraction(weight),
    )


def single_mode(widths, degree, numerator, denominator):
    assert degree >= 2 and degree % 2 == 0
    return row(widths, [0] * (degree // 2 - 1) + [1], weight=Fraction(numerator, denominator))


def programs(code_dir):
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(code_dir))

    def load(name):
        return importlib.import_module(f"chowla_{name}_certificate")

    subgrid = load("subgrid_single")
    original, spectral = subgrid.original, subgrid.moments
    sextic = load("sextic_septic")
    octic = load("octic")
    mixed = load("mixed_width")
    triple = load("three_width")
    return {
        "r0": [row((), [-c for c in original.projection] + spectral.ADDED[0])],
        "r1Grid": [
            row((i,), cs, width_denominator=subgrid.GRID)
            for i, cs in enumerate(subgrid.linear_coefficients(), 1)
        ],
        "r1Modes": [row((i,), [0] * 7 + cs) for i, cs in spectral.ADDED.items() if i],
        "r2": [
            row(widths, cs, width_denominator=40)
            for widths, cs in zip(original.pair_indices, original.quadratic_rows, strict=True)
        ],
        "r3": [row(widths, cs) for widths, cs in load("cubic_single").CUBIC_ROWS],
        "r4": [row((width,) * 4, cs) for width, cs in load("quartic_single").QUARTIC_ROWS],
        "r5": [row(widths, cs + [0] * (2 - len(cs))) for widths, cs in load("one_exception").QUINTIC_ROWS],
        "r6": [single_mode((a,) * k, degree, num, 10**7) for k, a, degree, num in sextic.PROFILES],
        "r7": [single_mode(widths, degree, num, octic.DENOMINATOR) for widths, degree, num in octic.PROFILES],
        "r8": [row(widths, cs, weight=Fraction(1, 10**9)) for widths, cs in mixed.PROFILES.items()],
        "r9": [row(widths, cs, weight=Fraction(1, 10**9)) for widths, cs in triple.PROFILES.items()],
    }, sextic.INHERITED_WEIGHT, original.linear_rows


def tex_rows(source, label, columns):
    table = source.split(r"\label{tab:" + label + "}", 1)[1].split(r"\bottomrule", 1)[0]
    marker = r"\endhead" if r"\endhead" in table else r"\midrule"
    body = table.split(marker, 1)[1]
    for line in body.splitlines():
        if not line.strip():
            continue
        cells = [cell.strip(" $") for cell in line.split(r"\\", 1)[0].split("&")]
        if len(cells) % columns:
            raise ValueError(f"unexpected layout in {label}: {line}")
        for i in range(0, len(cells), columns):
            group = cells[i : i + columns]
            if any(group):
                yield group


def number(cell):
    return Fraction(re.sub(r"\\frac\{(\d+)\}\{(\d+)\}", r"\1/\2", cell))


def widths(cell):
    if cell == r"\varnothing":
        return ()
    repeat = re.fullmatch(r"\((\d+)\)\^\{?(\d+)\}?", cell)
    if repeat:
        base, count = map(int, repeat.groups())
        return (base,) * count
    return tuple(map(int, cell.strip("()").split(",")))


def paper(path):
    source = path.read_text()
    r0_text = source.split(r"\item[(R0)]", 1)[1].split(r"\item[(R1)]", 1)[0]
    r0_groups = re.findall(r"\(([\d,\\\s-]+)\)", r0_text)
    r0 = [int(x) for group in r0_groups for x in re.findall(r"-?\d+", group)]
    quartic_and_quintic = list(tex_rows(source, "quartic", 3))
    return {
        "r0": [row((), r0)],
        "r1Modes": [
            row((int(a),), [0] * 7 + list(map(number, cs)))
            for a, *cs in sorted(tex_rows(source, "added", 5), key=lambda cells: int(cells[0]))
        ],
        "r2": [
            row((int(a), int(b)), list(map(number, cs)), width_denominator=40)
            for a, b, *cs in tex_rows(source, "quadratic", 7)
        ],
        "r3": [row(widths(a), list(map(number, cs))) for a, *cs in tex_rows(source, "cubic", 4)],
        "r4": [row(widths(a), list(map(number, cs))) for a, *cs in quartic_and_quintic[::2]],
        "r5": [row(widths(a), list(map(number, cs))) for a, *cs in quartic_and_quintic[1::2]],
        "r6": [
            single_mode((int(a),) * int(k), int(degree), int(num), 10**7)
            for k, a, degree, num in tex_rows(source, "septic", 4)
        ],
        "r7": [
            single_mode(widths(a), int(degree), int(num), 10**8)
            for a, degree, num in tex_rows(source, "octic", 3)
        ],
        "r8": [
            row(widths(a), [number(c) for c in cs if c], weight=Fraction(1, 10**9))
            for a, *cs in tex_rows(source, "mixed", 7)
        ],
        "r9": sorted(
            row(widths(a), list(map(number, cs)), weight=Fraction(1, 10**9))
            for a, *cs in tex_rows(source, "triple", 3)
        ),
    }


def rational(value):
    return str(value) if value.denominator == 1 else f"({value.numerator}/{value.denominator})"


def lean_list(values):
    return "[" + ", ".join(map(rational, values)) + "]"


def emit(module, rows, inherited_weight=None):
    imports = "import Mathlib.Data.Rat.Defs" if inherited_weight is not None else "import Chowla.Rows"
    lines = [imports, "", f"-- Generated by scripts/import_rows.py from {module}.", "", f"namespace Chowla.{module}", ""]
    if inherited_weight is not None:
        lines.extend([
            "structure RowData where",
            "  widths : List ℚ",
            "  coefficients : List ℚ",
            "  weight : ℚ",
            "  deriving DecidableEq",
            "",
            f"def inheritedWeight : ℚ := {rational(inherited_weight)}",
            "",
        ])
    else:
        lines.extend(["open Chowla.Rows (RowData)", ""])
    for name, data in rows.items():
        entries = [f"  ⟨{lean_list(ws)}, {lean_list(cs)}, {rational(w)}⟩" for ws, cs, w in data]
        chunks = [entries[i:i + 48] for i in range(0, len(entries), 48)]
        if len(chunks) == 1:
            lines.extend([f"def {name} : List RowData := [", ",\n".join(chunks[0]) + " ]", ""])
            continue
        chunk_names = []
        for i, chunk in enumerate(chunks):
            chunk_name = f"{name}Chunk{i + 1}"
            chunk_names.append(chunk_name)
            lines.extend([f"private def {chunk_name} : List RowData := [", ",\n".join(chunk) + " ]", ""])
        lines.extend([f"def {name} : List RowData :=", "  " + " ++ ".join(chunk_names), ""])
    lines.extend([f"end Chowla.{module}", ""])
    filename = "Rows" if inherited_weight is not None else "PaperRows"
    (MODULE_DIR / f"{filename}.lean").write_text("\n".join(lines))


def emit_linear_source(rows):
    if len(rows) != 159 or any(len(cs) != 7 for cs in rows):
        raise ValueError("expected 159 linear rows with seven coefficients each")
    lines = [
        "-- Generated by scripts/import_rows.py from the 160-grid Python module.",
        "namespace Chowla.Rows",
        "",
    ]
    chunk_names = []
    for i in range(0, len(rows), 32):
        name = f"linearSourceChunk{i // 32 + 1}"
        chunk_names.append(name)
        lines.append(f"private def {name} : Array (Array Int) := #[")
        lines.extend([",\n".join(f"  #{lean_list(cs)}" for cs in rows[i:i + 32]) + " ]", ""])
    lines.extend(["def linearSource : Array (Array Int) :=", "  " + " ++ ".join(chunk_names)])
    lines.extend(["", "end Chowla.Rows", ""])
    (MODULE_DIR / "LinearSource.lean").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path, help="chowla-nonvanishing directory of the pinned release")
    args = parser.parse_args()
    release = args.release.resolve()
    program_rows, inherited_weight, linear_source = programs(release / "code")
    paper_rows = paper(release / "paper" / "main.tex")
    emit("Rows", program_rows, inherited_weight)
    emit("PaperRows", paper_rows)
    emit_linear_source(linear_source)


if __name__ == "__main__":
    main()
