"""Audit Lean proof dependencies and the placement and goal type of native checks."""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
NATIVE = PACKAGE / "ZetaSixth" / "Native"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS_LINE = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)
COMPILER_AXIOM = re.compile(r"(.+)\._native\.native_decide\.ax_\d+_\d+")
DECLARATION = re.compile(
    r"^(theorem|lemma|def|abbrev|example|instance|namespace|end)\b(?:[ \t]+([\w.']+))?",
    re.MULTILINE,
)
NATIVE_TACTIC = re.compile(r"\bnative_decide\b")
BANNED = re.compile(r"\b(?:admit|sorry|axiom|native_decide|implemented_by|extern|unsafe)\b")


def code_only(source):
    """Remove comments and string contents while preserving line boundaries."""
    result = []
    pos = 0
    marker = re.compile(r'--[^\n]*|/-|"(?:\\.|[^"\\])*"', re.DOTALL)
    while match := marker.search(source, pos):
        result.append(source[pos : match.start()])
        end = match.end()
        if match.group() == "/-":
            depth = 1
            for delimiter in re.finditer(r"/-|-/", source[end:]):
                depth += 1 if delimiter.group() == "/-" else -1
                if depth == 0:
                    end += delimiter.end()
                    break
            else:
                raise ValueError("Unterminated Lean block comment.")
        result.append(" " + "\n" * source.count("\n", match.start(), end))
        pos = end
    return "".join([*result, source[pos:]])


def check_source_layout():
    files = [*(PACKAGE / "ZetaSixth").rglob("*.lean"), PACKAGE / "ZetaSixth.lean",
             PACKAGE / "Blueprint.lean"]
    for path in files:
        for token in BANNED.findall(code_only(path.read_text())):
            if token == "native_decide" and path.is_relative_to(NATIVE):
                continue
            raise ValueError(f"Unexpected {token} in {path.relative_to(PACKAGE)}.")


def native_declarations():
    """Find all Native theorem names and identify direct uses of the native tactic."""
    modules = set()
    theorems = set()
    direct = set()
    for path in sorted(NATIVE.rglob("*.lean")):
        modules.add(".".join(path.relative_to(PACKAGE).with_suffix("").parts))
        source = code_only(path.read_text())
        declarations = list(DECLARATION.finditer(source))
        namespaces = []
        counted = 0
        for index, decl in enumerate(declarations):
            if decl[1] == "namespace":
                namespaces.append(decl[2])
                continue
            if decl[1] == "end" and decl[2] and namespaces[-1:] == [decl[2]]:
                namespaces.pop()
                continue
            if decl[1] not in {"theorem", "lemma"}:
                continue
            name = ".".join([*namespaces, decl[2]])
            theorems.add(name)
            stop = declarations[index + 1].start() if index + 1 < len(declarations) else len(source)
            uses = NATIVE_TACTIC.findall(source, decl.end(), stop)
            if uses:
                direct.add(name)
                counted += len(uses)
        if counted != len(NATIVE_TACTIC.findall(source)):
            raise ValueError(f"Unaccounted native_decide invocation in {path.relative_to(PACKAGE)}.")
    return modules, theorems, direct


def verify_dependencies(output, expected, direct):
    reports = {}
    for name, text in AXIOMS_LINE.findall(output):
        dependencies = {word.strip() for word in text.split(",") if word.strip()}
        if name in reports and reports[name] != dependencies:
            raise ValueError(f"Conflicting axiom reports for {name}.")
        reports[name] = dependencies
    errors = [f"Missing axiom output for {name}." for name in sorted(expected - reports.keys())]
    for name, dependencies in reports.items():
        for dependency in sorted(dependencies - STANDARD):
            emitted = COMPILER_AXIOM.fullmatch(dependency)
            if emitted and emitted[1] in direct and dependency in reports.get(emitted[1], set()):
                continue
            errors.append(f"{name} depends on unapproved axiom {dependency}.")
    if errors:
        raise ValueError("\n".join(errors))
    return len(reports)


def run_lean(path):
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=PACKAGE, check=True, text=True,
        stdout=subprocess.PIPE,
    ).stdout


def main():
    check_source_layout()
    modules, theorems, direct = native_declarations()
    audit = PACKAGE / "scripts" / "axioms.lean"
    expected = set(re.findall(r"^#print axioms ([\w.']+)$", audit.read_text(), re.MULTILINE))
    output = run_lean(audit)
    if modules:
        imports = [f"import {module}" for module in sorted(modules)]
        prints = [f"#print axioms {name}" for name in sorted(theorems)]
        # A proof of another proposition cannot inhabit this Boolean equality.
        checks = [f"example : ∃ b : Bool, b = true := ⟨_, {name}⟩" for name in sorted(direct)]
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "NativeAudit.lean"
            source.write_text("\n".join([*imports, "", *prints, *checks, ""]))
            output += run_lean(source)
    print(output, end="")
    count = verify_dependencies(output, expected | theorems, direct)
    print(f"Verified {count} declarations and {len(direct)} native Boolean equalities.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or "", end="")
        sys.exit(str(error))
    except (ValueError, OSError) as error:
        sys.exit(str(error))
