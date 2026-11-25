#!/usr/bin/env python3
"""Audit the kernel axioms of the Chowla formalisation."""

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "scripts" / "axioms.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_FACTS = {
    "Chowla.Native.stage1_central_checked",
    "Chowla.Native.stage1_linear_0_80_checked",
    "Chowla.Native.stage1_linear_80_120_checked",
    "Chowla.Native.stage1_linear_120_160_checked",
    "Chowla.Native.stage1_linear_160_200_checked",
    "Chowla.Native.stage1_linear_200_240_checked",
    "Chowla.Native.stage1_linear_240_280_checked",
    "Chowla.Native.stage1_linear_280_320_checked",
    "Chowla.Native.stage1_linear_320_360_checked",
    "Chowla.Native.stage1_linear_360_400_checked",
    "Chowla.Native.stage1_linear_400_440_checked",
    "Chowla.Native.stage1_linear_440_480_checked",
    "Chowla.Native.stage1_linear_480_520_checked",
    "Chowla.Native.stage1_linear_520_560_checked",
    "Chowla.Native.stage1_linear_560_600_checked",
    "Chowla.Native.stage1_linear_600_640_checked",
    "Chowla.Native.stage1_linear_640_650_checked",
    "Chowla.Native.stage1_quadratic_checked",
    "Chowla.Native.stage2_checked",
    "Chowla.Native.stage3_checked",
    "Chowla.Native.stage4_checked",
    "Chowla.Native.stage5_checked",
    "Chowla.Native.stage6_central_checked",
    "Chowla.Native.stage6_gram_0_5_checked",
    "Chowla.Native.stage6_gram_5_8_checked",
    "Chowla.Native.stage6_gram_8_10_checked",
    "Chowla.Native.stage6_gram_10_13_checked",
    "Chowla.Native.stage7_central_checked",
    "Chowla.Native.stage7_gram_0_10_checked",
    "Chowla.Native.stage7_gram_10_20_checked",
    "Chowla.Native.stage7_gram_20_35_checked",
    "Chowla.Native.stage7_gram_35_50_checked",
    "Chowla.Native.stage7_gram_50_65_checked",
    "Chowla.Native.stage7_gram_65_80_checked",
    "Chowla.Native.stage7_gram_80_95_checked",
    "Chowla.Native.stage7_gram_95_103_checked",
    "Chowla.Native.stage8_central_checked",
    "Chowla.Native.stage8_gram_0_6_checked",
    "Chowla.Native.stage8_gram_6_12_checked",
    "Chowla.Native.stage8_gram_12_18_checked",
    "Chowla.Native.stage8_gram_18_26_checked",
}
NATIVE_ASSEMBLY = {
    "Chowla.certificate_stage",
    "Chowla.certificate",
    "Chowla.main_class_of",
    "Chowla.main_of",
}


def compiler_axiom(name):
    return f"{name}._native.native_decide.ax_1_1"


RESULT = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)


def check_native_sources():
    declarations = set()
    calls = 0
    for source in (ROOT / "Chowla").rglob("*.lean"):
        text = source.read_text()
        count = len(re.findall(r"^\s*native_decide\s*$", text, re.MULTILINE))
        if source.parent.name == "Native":
            declarations.update(
                f"Chowla.Native.{name}" for name in re.findall(r"^theorem (\w+)", text, re.MULTILINE)
            )
            calls += count
        elif count:
            raise SystemExit(f"Compiler-backed proof outside Chowla/Native: {source}")
    if declarations != NATIVE_FACTS or calls != len(NATIVE_FACTS):
        raise SystemExit("Native source and compiler axiom allowlist differ")


def main():
    check_native_sources()
    expected = set(re.findall(r"^#print axioms (\S+)$", AUDIT.read_text(), re.MULTILINE))
    result = subprocess.run(
        ["lake", "env", "lean", str(AUDIT)], cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True
    )
    print(result.stdout, end="")
    reports = dict(RESULT.findall(result.stdout))
    missing = expected - reports.keys()
    if missing:
        raise SystemExit(f"Missing axiom reports for {', '.join(sorted(missing))}")
    omitted = (NATIVE_FACTS | NATIVE_ASSEMBLY) - expected
    if omitted:
        raise SystemExit(f"Required facts missing from the audit: {', '.join(sorted(omitted))}")
    native_axioms = {compiler_axiom(fact) for fact in NATIVE_FACTS}
    for name, text in reports.items():
        used = {part.strip() for part in text.split(",") if part.strip()}
        allowed = ALLOWED
        if name in NATIVE_FACTS:
            axiom = compiler_axiom(name)
            if axiom not in used:
                raise SystemExit(f"Expected the compiler axiom {axiom} on {name}")
            allowed = allowed | {axiom}
        elif name in NATIVE_ASSEMBLY:
            allowed = allowed | native_axioms
        if unexpected := used - allowed:
            raise SystemExit(f"{name} uses {', '.join(sorted(unexpected))}")


if __name__ == "__main__":
    main()
