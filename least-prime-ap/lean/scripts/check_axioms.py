"""Check source layout, native goals and kernel dependencies on the pinned toolchain."""

import re
import subprocess
import tempfile
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
HEADLINES = {
    "LeastPrime.p6_Tin",
    "LeastPrime.q5_Tout",
    "LeastPrime.main_of_cited",
    "LeastPrime.density_lower_of_cited",
    "LeastPrime.density_upper_of_cited",
}
SOUNDNESS = {
    "LeastPrime.Checker.probabilityBound_sound",
    "LeastPrime.Checker.checkWindow_sound",
    "LeastPrime.Checker.checkLowerSlice_sound",
    "LeastPrime.Checker.checkLowerSixSlices_sound",
    "LeastPrime.Checker.probabilityBound_sixSlices",
    "LeastPrime.lowerP_sound",
    "LeastPrime.upperQ_sound",
}
REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)
COMPILER_AXIOM = re.compile(r"(.+)\._native\.native_decide\.ax_\d+_\d+")
NATIVE_GOAL = re.compile(
    r"^(?:theorem|lemma) (\w+)\s*:\s*"
    r"((?:checkWindow\s+\.(?:lower|upper)(?:\s+\d+){4}|"
    r"checkLowerSlice\s+(?:false|true)(?:\s+\d+){5})\s*=\s*true)\s*:=\s*by\s+native_decide\b",
    re.MULTILINE,
)
BANNED = re.compile(r"\b(?:sorry|admit|axiom|unsafe|extern|implemented_by|native_decide|Float)\b")


def code_only(source):
    """Strip Lean comments and strings while keeping declaration line breaks."""
    marker = re.compile(r'--[^\n]*|/-|"(?:\\.|[^"\\])*"', re.DOTALL)
    pieces = []
    start = 0
    while match := marker.search(source, start):
        pieces.append(source[start:match.start()])
        end = match.end()
        if match.group() == "/-":
            depth = 1
            for delimiter in re.finditer(r"/-|-/", source[end:]):
                depth += 1 if delimiter.group() == "/-" else -1
                if not depth:
                    end += delimiter.end()
                    break
            else:
                raise ValueError("Unterminated Lean comment")
        pieces.append(" " + "\n" * source.count("\n", match.start(), end))
        start = end
    return "".join([*pieces, source[start:]])


def source_checks():
    native_root = PACKAGE / "LeastPrime/Native"
    files = sorted((PACKAGE / "LeastPrime").rglob("*.lean")) + [PACKAGE / "LeastPrime.lean"]
    direct = {}
    for path in files:
        source = code_only(path.read_text())
        if path.is_relative_to(native_root):
            goals = NATIVE_GOAL.findall(source)
            if (len(goals) != len(re.findall(r"\bnative_decide\b", source)) or
                    len(goals) != len(re.findall(r"^(?:theorem|lemma)\b", source, re.MULTILINE)) or
                    "namespace LeastPrime.Native" not in source):
                raise ValueError(f"Unaccounted native declaration in {path.relative_to(PACKAGE)}")
            for suffix, goal in goals:
                name = f"LeastPrime.Native.{suffix}"
                if name in direct:
                    raise ValueError(f"Duplicate native check {name}")
                direct[name] = f"LeastPrime.Checker.{goal}"
            source = source.replace("native_decide", " ")
        if forbidden := BANNED.search(source):
            raise ValueError(f"Unexpected {forbidden.group()} in {path.relative_to(PACKAGE)}")
    return direct


def lean_check(source):
    result = subprocess.run(
        ["lake", "env", "lean", str(source)],
        cwd=PACKAGE,
        stdout=subprocess.PIPE,
        text=True,
        check=False,
    )
    print(result.stdout, end="")
    result.check_returncode()
    return result.stdout


def main():
    direct = source_checks()
    audit = PACKAGE / "scripts/axioms.lean"
    expected = set(re.findall(r"^#print axioms (\S+)$", audit.read_text(), re.MULTILINE))
    missing = (HEADLINES | SOUNDNESS | direct.keys()) - expected
    if missing:
        raise ValueError(f"Missing axiom coverage for {sorted(missing)}")
    if direct:
        # The annotation type-checks the exact compiled Boolean goal for each native lemma.
        with tempfile.TemporaryDirectory(prefix="least-prime-audit-") as temp:
            source = Path(temp) / "NativeGoals.lean"
            examples = [f"example : {goal} := {name}" for name, goal in direct.items()]
            source.write_text("\n".join(["import LeastPrime", "", *examples, ""]))
            lean_check(source)
    reports = {
        name: {item.strip() for item in dependencies.split(",") if item.strip()}
        for name, dependencies in REPORT.findall(lean_check(audit))
    }
    if reports.keys() != expected:
        raise ValueError(f"Unexpected axiom report coverage, missing {sorted(expected - reports.keys())}")
    for name, dependencies in reports.items():
        for dependency in sorted(dependencies - STANDARD):
            emitted = COMPILER_AXIOM.fullmatch(dependency)
            if (name not in SOUNDNESS and emitted and emitted[1] in direct
                    and dependency in reports[emitted[1]]):
                continue
            raise ValueError(f"{name} depends on unapproved axiom {dependency}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
