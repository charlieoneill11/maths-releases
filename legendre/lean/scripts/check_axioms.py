"""Check Lean's axiom reports against the project allowlist."""

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)
PRINT_AXIOMS = re.compile(r"^#print axioms (\S+)$", re.MULTILINE)
TOKEN = re.compile(r'--[^\n]*|/-|"(?:\\.|[^"\\])*"', re.DOTALL)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|ofReduceBool|trustCompiler)\b")
NATIVE = re.compile(r"\bnative_decide\b")
NATIVE_AXIOM = re.compile(r"(.+)\._native\.native_decide\.ax_\d+_\d+")
DECLARATION = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(namespace|section|end|theorem|lemma|def|abbrev|example|instance)\b(?:[ \t]+([\w.']+))?",
    re.MULTILINE,
)

NATIVE_TYPE_CHECK = """\
open Lean Elab Command in
elab "#audit_native " thm:ident " using " checker:ident : command => do
  let type := (← getConstInfo thm.getId).type
  unless type.isAppOfArity ``Eq 3 do
    throwError "{thm.getId} must conclude a Boolean equality"
  let #[ty, lhs, rhs] := type.getAppArgs | throwError "Expected an equality"
  unless ty.isConstOf ``Bool && rhs.isConstOf ``Bool.true do
    throwError "{thm.getId} must conclude checker data = true"
  unless lhs.isApp && lhs.getAppFn.isConstOf checker.getId do
    throwError "{thm.getId} must check {checker.getId}"
"""


def code_only(source):
    """Remove comments and strings before checking for Lean commands."""
    chunks = []
    start = 0
    while match := TOKEN.search(source, start):
        chunks.append(source[start:match.start()])
        start = match.end()
        if match[0] == "/-":
            depth = 1
            for delimiter in re.finditer(r"/-|-/", source[start:]):
                depth += 1 if delimiter[0] == "/-" else -1
                if depth == 0:
                    start += delimiter.end()
                    break
            else:
                raise ValueError("unterminated Lean block comment")
        chunks.append(" " + "\n" * source.count("\n", match.start(), start))
    return "".join([*chunks, source[start:]])


def source_layout():
    """Find every proof in Native and every direct call to the native tactic."""
    sources = [PACKAGE / "Blueprint.lean", PACKAGE / "Legendre.lean", *(PACKAGE / "Legendre").rglob("*.lean")]
    native_modules = set()
    native_proofs = set()
    calls = set()
    for path in sources:
        relative = path.relative_to(PACKAGE)
        source = code_only(path.read_text())
        if match := FORBIDDEN.search(source):
            raise ValueError(f"{relative} contains {match[0]}")
        count = len(NATIVE.findall(source))
        if relative.parts[:2] != ("Legendre", "Native"):
            if count:
                raise ValueError(f"{relative} uses native_decide outside Legendre/Native")
            continue

        native_modules.add(".".join(relative.with_suffix("").parts))
        scopes = []
        decls = list(DECLARATION.finditer(source))
        for index, decl in enumerate(decls):
            kind, ident = decl.groups()
            if kind == "namespace":
                scopes.append(ident)
            elif kind == "section":
                scopes.append(None)
            elif kind == "end" and scopes:
                scopes.pop()
            elif kind in {"theorem", "lemma"} and ident:
                name = ".".join([*(scope for scope in scopes if scope), ident])
                native_proofs.add(name)
                stop = decls[index + 1].start() if index + 1 < len(decls) else len(source)
                used = len(NATIVE.findall(source[decl.end():stop]))
                if used > 1:
                    raise ValueError(f"Multiple native checks in {name}")
                if used:
                    calls.add(name)
                    count -= 1
        if count:
            raise ValueError(f"Unaccounted native_decide use in {relative}")
    return native_modules, native_proofs, calls


def main():
    modules, native_proofs, calls = source_layout()
    registry = json.loads((PACKAGE / "scripts" / "native_checks.json").read_text())
    if set(registry) != calls:
        raise ValueError(f"Native audit registry differs from the source for {sorted(set(registry) ^ calls)}")
    soundness = {entry["soundness"] for entry in registry.values()}

    script = PACKAGE / "scripts" / "axioms.lean"
    source = script.read_text()
    printed = set(PRINT_AXIOMS.findall(source))
    expected = printed | native_proofs | soundness
    imports = [f"import {module}" for module in sorted(modules)]
    checks = [f"#audit_native {name} using {entry['checker']}" for name, entry in sorted(registry.items())]
    reports_to_add = [f"#print axioms {name}" for name in sorted(expected - printed)]
    with tempfile.TemporaryDirectory() as temp:
        audit = Path(temp) / "AxiomAudit.lean"
        audit.write_text("\n".join(["import Lean", *imports, source, NATIVE_TYPE_CHECK, *checks, *reports_to_add]))
        result = subprocess.run(
            ["lake", "env", "lean", str(audit)], cwd=PACKAGE, stdout=subprocess.PIPE, text=True,
        )
    print(result.stdout, end="")
    result.check_returncode()

    reports = {}
    for match in REPORT.finditer(result.stdout):
        reports[match[1]] = {name.strip() for name in (match[2] or "").split(",") if name.strip()}
    if missing := expected - reports.keys():
        raise ValueError(f"Missing axiom reports for {', '.join(sorted(missing))}")
    permitted_native = {
        axiom for name in calls for axiom in reports[name]
        if (match := NATIVE_AXIOM.fullmatch(axiom)) and match[1] == name
    }
    for theorem, axioms in reports.items():
        allowed = STANDARD_AXIOMS if theorem in soundness else STANDARD_AXIOMS | permitted_native
        if unapproved := axioms - allowed:
            raise ValueError(f"{theorem} uses {', '.join(sorted(unapproved))}")
    print(f"Verified the axiom allowlist for {len(reports)} declarations and {len(calls)} native checks.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
