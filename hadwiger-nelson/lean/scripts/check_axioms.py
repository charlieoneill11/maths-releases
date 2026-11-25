"""Check the output of `lake env lean scripts/axioms.lean` on Lean 4.29.1."""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
# List the exact generated native_decide axiom names separately for each theorem.
NATIVE_AXIOMS = {
    "HadwigerNelson.edges_le_245510": set(),
    "HadwigerNelson.points_le_10689_of_cited": set(),
    "HadwigerNelson.dist_three_fifths_four_fifths": set(),
    "HadwigerNelson.unit_triangle_side_lengths": set(),
    "HadwigerNelson.unit_triangle_no_two_colouring": set(),
    "HadwigerNelson.edges_le_245510_one_colour_false": set(),
    "HadwigerNelson.points_le_10689_one_colour_false": set(),
}
ANGULAR_CHECKS = tuple(
    f"HadwigerNelson.Angular.Native.block{index:03}" for index in range(3, 9)
)
ANGULAR_AXIOMS = {f"{name}._native.native_decide.ax_1_1" for name in ANGULAR_CHECKS}
for name in ANGULAR_CHECKS:
    NATIVE_AXIOMS[name] = {f"{name}._native.native_decide.ax_1_1"}
NATIVE_AXIOMS["HadwigerNelson.edges_le_245269"] = ANGULAR_AXIOMS
LAYOUT_CHECK = "HadwigerNelson.Stars.BoxCheck.sourceBoxes_checked"
LAYOUT_AXIOMS = {f"{LAYOUT_CHECK}._native.native_decide.ax_1_1"}
NATIVE_AXIOMS[LAYOUT_CHECK] = LAYOUT_AXIOMS
NATIVE_AXIOMS["HadwigerNelson.Stars.BoxCheck.complete_layout"] = LAYOUT_AXIOMS
STAR_CHECK = "HadwigerNelson.Stars.BoxCheck.complete_checked"
STAR_AXIOMS = {f"{STAR_CHECK}._native.native_decide.ax_1_1"}
NATIVE_AXIOMS[STAR_CHECK] = STAR_AXIOMS
NATIVE_AXIOMS["HadwigerNelson.edges_le_245510"] = ANGULAR_AXIOMS | LAYOUT_AXIOMS | STAR_AXIOMS
POINT_BOX_CHECK = "HadwigerNelson.Certificate.ParameterBoxes.boxes_checked"
POINT_BOX_AXIOMS = {f"{POINT_BOX_CHECK}._native.native_decide.ax_1_1"}
NATIVE_AXIOMS[POINT_BOX_CHECK] = POINT_BOX_AXIOMS
NATIVE_AXIOMS["HadwigerNelson.Certificate.point_bound_lt_one"] = POINT_BOX_AXIOMS
PARTIAL_LAYOUT = "HadwigerNelson.Stars.PartialCheck.Layout.checked"
NATIVE_AXIOMS[PARTIAL_LAYOUT] = {f"{PARTIAL_LAYOUT}._native.native_decide.ax_1_1"}
PARTIAL_ANGULAR_CHECKS = tuple(
    f"HadwigerNelson.Angular.Partial.Native.block{index:03}" for index in range(3, 9)
)
PARTIAL_STAR_CHECKS = tuple(
    f"HadwigerNelson.Stars.PartialCheck.Native.shard{index}" for index in range(4)
)
POINT_TABLE_CHECKS = (
    "HadwigerNelson.Certificate.Hole.means_checked",
    "HadwigerNelson.Certificate.Hole.packing_checked",
    "HadwigerNelson.Centres.Quadrature.Native.smallIntervals",
    "HadwigerNelson.Centres.Quadrature.Native.mediumCoarse",
    "HadwigerNelson.Centres.Quadrature.Native.mediumFine",
)
for name in PARTIAL_ANGULAR_CHECKS + PARTIAL_STAR_CHECKS + POINT_TABLE_CHECKS:
    NATIVE_AXIOMS[name] = {f"{name}._native.native_decide.ax_1_1"}
POINT_CHECKS = (POINT_BOX_CHECK, PARTIAL_LAYOUT, *PARTIAL_ANGULAR_CHECKS, *PARTIAL_STAR_CHECKS, *POINT_TABLE_CHECKS)
NATIVE_AXIOMS["HadwigerNelson.points_le_10689_of_cited"] = set().union(
    *(NATIVE_AXIOMS[name] for name in POINT_CHECKS)
)
REPORT = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*$",
    re.MULTILINE,
)
GENERATED = re.compile(r"(.+)\._native\.native_decide\.ax_\d+_\d+")
TOKEN = re.compile(r'--[^\n]*|/-|"(?:\\.|[^"\\])*"', re.DOTALL)
DECL = re.compile(r"^\s*(namespace|section|end|theorem|lemma|def|abbrev|example|instance)\b(?:[ \t]+([\w.']+))?", re.MULTILINE)
BANNED = re.compile(r"\b(?:sorry|admit|axiom|implemented_by|extern|unsafe|Float|Float32|native_decide)\b")


def code_only(source):
    """Strip nested comments and quoted strings without changing line boundaries."""
    result = []
    pos = 0
    while match := TOKEN.search(source, pos):
        result.append(source[pos:match.start()])
        end = match.end()
        if match[0] == "/-":
            depth = 1
            for delim in re.finditer(r"/-|-/", source[end:]):
                depth += 1 if delim[0] == "/-" else -1
                if depth == 0:
                    end += delim.end()
                    break
            else:
                raise ValueError("unterminated block comment")
        result.append(" " + "\n" * source.count("\n", match.start(), end))
        pos = end
    return "".join([*result, source[pos:]])


def native_theorems(source):
    """Collect named Native theorems and identify the ones invoking native_decide."""
    stack, theorems, direct = [], set(), set()
    declarations = list(DECL.finditer(source))
    consumed = 0
    for i, decl in enumerate(declarations):
        kind, name = decl.groups()
        if kind in {"namespace", "section"}:
            stack.append(name if kind == "namespace" else None)
        elif kind == "end" and stack:
            stack.pop()
        elif kind in {"theorem", "lemma"} and name:
            full = ".".join([*(s for s in stack if s), name])
            theorems.add(full)
            stop = declarations[i+1].start() if i+1 < len(declarations) else len(source)
            calls = len(re.findall(r"\bnative_decide\b", source[decl.end():stop]))
            if calls:
                direct.add(full)
                consumed += calls
    if consumed != len(re.findall(r"\bnative_decide\b", source)):
        raise ValueError("native_decide outside a recognised named theorem")
    if len(theorems) != len(re.findall(r"\b(?:theorem|lemma)\b", source)):
        raise ValueError("unrecognised Native theorem declaration")
    return theorems, direct


def dependencies(output, expected, direct):
    reports = {}
    for match in REPORT.finditer(output):
        name, raw = match.groups()
        if name in reports:
            raise ValueError(f"duplicate audit result for {name}")
        reports[name] = {a.strip() for a in (raw or "").split(",") if a.strip()}
    if reports.keys() != expected.keys():
        raise ValueError(f"missing reports {sorted(expected.keys() - reports.keys())}; "
                         f"unexpected reports {sorted(reports.keys() - expected.keys())}")
    errors = []
    for name, axioms in reports.items():
        actual = axioms - STANDARD
        for ax in sorted(actual | expected[name]):
            owner = GENERATED.fullmatch(ax)
            if not owner or owner[1] not in direct or ax not in expected.get(owner[1], set()):
                errors.append(f"{name}: unapproved axiom {ax}")
        if actual != expected[name]:
            errors.append(f"{name}: unexpected {sorted(actual - expected[name])}, "
                          f"missing {sorted(expected[name] - actual)}")
    if errors:
        raise ValueError("\n".join(errors))


def source_manifest():
    native = PACKAGE / "HadwigerNelson/Native"
    modules = {}
    errors = []
    files = list(PACKAGE.glob("*.lean"))
    for directory in PACKAGE.iterdir():
        if directory.is_dir() and not directory.name.startswith(".") and directory.name != "scripts":
            files.extend(directory.rglob("*.lean"))
    for path in sorted(files):
        if path.name == "lakefile.lean":
            continue
        source = code_only(path.read_text())
        forbidden = set(BANNED.findall(source))
        if path.is_relative_to(native):
            forbidden.discard("native_decide")
            names, direct = native_theorems(source)
            missing = names - NATIVE_AXIOMS.keys()
            if missing:
                errors.append(f"{path.name}: missing per-theorem allowlists {sorted(missing)}")
            mod = ".".join(path.relative_to(PACKAGE).with_suffix("").parts)
            modules.update((name, mod) for name in direct)
        if forbidden:
            errors.append(f"{path.relative_to(PACKAGE)}: forbidden {sorted(forbidden)}")
    return modules, errors


def check_goal_types(direct):
    if not direct:
        return
    imports = [f"import {m}" for m in sorted(set(direct.values()))]
    checks = [f"example : ∃ b : Bool, b = true := ⟨_, {n}⟩" for n in sorted(direct)]
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "NativeGoalTypes.lean"
        path.write_text("\n".join([*imports, "", *checks, ""]))
        subprocess.run(["lake", "env", "lean", str(path)], cwd=PACKAGE, check=True)


def main(log):
    printed = re.findall(r"^#print axioms ([\w.']+)$", code_only((PACKAGE / "scripts/axioms.lean").read_text()), re.MULTILINE)
    if sorted(printed) != sorted(NATIVE_AXIOMS):
        raise ValueError("scripts/axioms.lean and the per-theorem allowlists disagree")
    direct, errors = source_manifest()
    output = log.read_text()
    if re.search(r"^(?:error:|.*:\d+:\d+: error:)", output, re.MULTILINE):
        errors.append("Lean reported an elaboration error")
    try:
        dependencies(output, NATIVE_AXIOMS, direct)
    except ValueError as error:
        errors.append(str(error))
    if errors:
        raise ValueError("\n".join(errors))
    check_goal_types(direct)
    print(f"Verified {len(printed)} declarations and {len(direct)} native Boolean checks.")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: python3 scripts/check_axioms.py AXIOM_LOG")
    try:
        main(Path(sys.argv[1]))
    except (ValueError, OSError, subprocess.CalledProcessError) as err:
        sys.exit(str(err))
