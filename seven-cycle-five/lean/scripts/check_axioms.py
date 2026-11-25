"""Check the pinned Lean compiler's #print axioms output and native goal types."""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PUBLIC_BOUNDS = {"SevenCycle.card_le_112", "SevenCycle.card_le_392"}
REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)
COMPILER_AXIOM = re.compile(r"(.+)\._native\.native_decide\.ax_\d+_\d+")
DECLARATION = re.compile(r"^(theorem|lemma|def|abbrev|example|instance|namespace|end)\b(?:[ \t]+([\w.']+))?", re.MULTILINE)
NATIVE_TACTIC = re.compile(r"\bnative_decide\b")


def code_only(source):
    """Remove comments and string contents while preserving line boundaries."""
    result = []
    pos = 0
    marker = re.compile(r'--[^\n]*|/-|"(?:\\.|[^"\\])*"', re.DOTALL)
    while match := marker.search(source, pos):
        result.append(source[pos:match.start()])
        end = match.end()
        if match.group() == "/-":
            depth = 1
            for delimiter in re.finditer(r"/-|-/", source[end:]):
                depth += 1 if delimiter.group() == "/-" else -1
                if depth == 0:
                    end += delimiter.end()
                    break
            else:
                raise ValueError("unterminated Lean block comment")
        result.append(" " + "\n" * source.count("\n", match.start(), end))
        pos = end
    return "".join([*result, source[pos:]])


def native_declarations():
    """Identify the named theorems in the Native modules and every direct tactic use."""
    theorems = set()
    direct = {}
    for path in sorted((PACKAGE / "SevenCycle/Native").rglob("*.lean")):
        source = code_only(path.read_text())
        namespaces = []
        module = ".".join(path.relative_to(PACKAGE).with_suffix("").parts)
        decls = list(DECLARATION.finditer(source))
        count = 0
        for index, decl in enumerate(decls):
            if decl[1] == "namespace":
                namespaces.append(decl[2])
            elif decl[1] == "end" and namespaces:
                namespaces.pop()
            if decl[1] not in {"theorem", "lemma"}:
                continue
            name = ".".join([*namespaces, decl[2]])
            theorems.add(name)
            stop = decls[index + 1].start() if index + 1 < len(decls) else len(source)
            uses = NATIVE_TACTIC.findall(source, decl.end(), stop)
            if uses:
                direct[name] = module
                count += len(uses)
        if count != len(NATIVE_TACTIC.findall(source)):
            raise ValueError(f"unaccounted native_decide invocation in {path}")
    return theorems, direct


def check_source_layout():
    roots = [PACKAGE / "SevenCycle", PACKAGE / "SevenCycleRuntime"]
    files = [path for root in roots for path in root.rglob("*.lean")]
    files.extend([PACKAGE / "SevenCycle.lean", PACKAGE / "SevenCycleRuntime.lean"])
    native = PACKAGE / "SevenCycle/Native"
    banned = re.compile(r"\b(?:admit|sorry|axiom|native_decide|implemented_by|extern)\b")
    for path in files:
        source = path.read_text()
        if banned.search(source):
            for token in banned.findall(code_only(source)):
                if token == "native_decide" and path.is_relative_to(native):
                    continue
                raise ValueError(f"unexpected {token} in {path.relative_to(PACKAGE)}")


def verify_dependencies(output, expected, direct):
    reports = {}
    for match in REPORT.finditer(output):
        names = {word.strip() for word in (match[2] or "").split(",") if word.strip()}
        if match[1] in reports and reports[match[1]] != names:
            raise ValueError(f"conflicting reports for {match[1]}")
        reports[match[1]] = names
    missing = expected - reports.keys()
    errors = [f"missing #print axioms result for {name}" for name in sorted(missing)]
    for name, dependencies in reports.items():
        for dependency in sorted(dependencies - STANDARD):
            emitted = COMPILER_AXIOM.fullmatch(dependency)
            if emitted and emitted[1] in direct and dependency in reports.get(emitted[1], set()):
                continue
            errors.append(f"{name} depends on unapproved axiom {dependency}")
    if errors:
        raise ValueError("\n".join(errors))
    return len(reports)


def check_goal_types(direct):
    # The existential's metavariable is inferred from the actual compiled
    # theorem. Lean accepts it exactly when its conclusion is b = true.
    imports = [f"import {module}" for module in sorted(set(direct.values()))]
    checks = [f"example : ∃ b : Bool, b = true := ⟨_, {name}⟩" for name in sorted(direct)]
    with tempfile.TemporaryDirectory() as temp:
        source = Path(temp) / "NativeGoalTypes.lean"
        source.write_text("\n".join([*imports, "", *checks, ""]))
        subprocess.run(["lake", "env", "lean", str(source)], cwd=PACKAGE, check=True)


def main():
    if len(sys.argv) != 2:
        raise ValueError("expected the path to the log produced by lean scripts/axioms.lean")
    theorems, direct = native_declarations()
    printed = set(re.findall(
        r"^#print axioms ([\w.']+)$", (PACKAGE / "scripts/axioms.lean").read_text(), re.MULTILINE
    ))
    count = verify_dependencies(Path(sys.argv[1]).read_text(), PUBLIC_BOUNDS | theorems | printed, direct)
    check_source_layout()
    check_goal_types(direct)
    print(f"Verified the dependencies of {count} declarations and {len(direct)} native Boolean equalities.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
