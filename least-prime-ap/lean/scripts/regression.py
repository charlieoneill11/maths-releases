"""Compare the executable Lean port with the pinned, untrusted C++ oracle."""

import argparse
import hashlib
import random
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
ORACLE_SHA256 = "83afd8be000a59fffffd3e648658e584fdec29924a9f2de9e2a0e37a01f131aa"
UNIT = 1_000_000
CPP_WRAPPER = r'''
#define main oracle_main
#include "oracle.cpp"
#undef main
#include <sstream>
#include <string>

int extension(const Intervals& target, int level, Bound bound) {
    if (target.empty()) return 0;
    if (target.front().first == 0) return unit;
    if (level == 0) return bound == Bound::lower ? 0 : unit;
    if (bound == Bound::upper) return target.back().second;
    int length = 0;
    for (const auto& [low, high] : target) length += high - low;
    return length;
}

int main() {
    std::string line;
    while (std::getline(std::cin, line)) {
        std::istringstream row(line);
        int side, level, low, high;
        row >> side >> level;
        Intervals target;
        while (row >> low >> high) target.emplace_back(low, high);
        const auto bound = side == 0 ? Bound::lower : Bound::upper;
        // Levels zero and one are exact formulas from the reading of E and F.
        // Upper level six extends the upper level-five cell count for this regression.
        const std::array<int, 7> bins = side == 0
            ? std::array<int, 7>{0, 0, 0, 100, 220, 320, 450}
            : std::array<int, 7>{0, 0, 0, 400, 500, 600, 600};
        std::cout << (level < 2 ? extension(target, level, bound)
            : probability_bound(target, level, bound, bins)) << std::endl;
    }
}
'''


def random_targets(count, seed):
    rng = random.Random(seed)
    for _ in range(count):
        # Short gaps make the full published cell schedules feasible on every sample.
        left = []
        start = rng.randrange(1, 2200)
        for _ in range(rng.randrange(5)):
            end = start + rng.randrange(3500)
            left.append((start, end))
            start = end + rng.randrange(1, 240)
        center = [(start, UNIT - start)]
        yield left + center + [(UNIT - high, UNIT - low) for low, high in reversed(left)]


def regression_cases(count, seed):
    for target in random_targets(count, seed):
        for side in range(2):
            for level in range(7):
                yield side, level, target
    edge_targets = [
        [],
        [(0, 0), (UNIT, UNIT)],
        [(0, UNIT)],
        [(1, UNIT - 1)],
        [(UNIT // 2, UNIT // 2)],
        [(142857, 200000), (800000, 857143)],
    ]
    for side in range(2):
        for level in range(4):
            for target in edge_targets:
                yield side, level, target


def run(*args, **kwargs):
    return subprocess.run(args, cwd=PACKAGE, text=True, check=True, **kwargs)


def build_executables(source, directory):
    if hashlib.sha256(source.read_bytes()).hexdigest() != ORACLE_SHA256:
        raise ValueError("The oracle checksum differs from the release verifier")
    shutil.copyfile(source, directory / "oracle.cpp")
    wrapper = directory / "oracle_wrapper.cpp"
    wrapper.write_text(CPP_WRAPPER)
    cpp_exe = directory / "oracle"
    run("c++", "-O3", "-std=c++17", wrapper, "-o", cpp_exe)
    lean_c = directory / "Regression.c"
    lean_exe = directory / "checker"
    run("lake", "build", "LeastPrime.Checker.Compute")
    run("lake", "env", "lean", "-c", lean_c, "scripts/Regression.lean")
    run("lake", "env", "leanc", "-O3", "-o", lean_exe,
        ".lake/build/ir/LeastPrime/Checker/Compute.c", lean_c)
    return cpp_exe, lean_exe


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("oracle_source", type=Path)
    parser.add_argument("--count", type=int, default=300)
    parser.add_argument("--seed", type=int, default=20261124)
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    cases = list(regression_cases(args.count, args.seed))
    data = "".join(" ".join(str(x) for x in [side, level, *(x for pair in target for x in pair)])
                   + "\n" for side, level, target in cases)
    with tempfile.TemporaryDirectory(prefix="least-prime-regression-") as temp:
        cpp_exe, lean_exe = build_executables(args.oracle_source.resolve(), Path(temp))
        start = time.monotonic()
        cpp = run(cpp_exe, input=data, capture_output=True, timeout=args.timeout).stdout.splitlines()
        cpp_time = time.monotonic() - start
        start = time.monotonic()
        lean = run(lean_exe, input=data, capture_output=True, timeout=args.timeout).stdout.splitlines()
        lean_time = time.monotonic() - start
    if len(cpp) != len(cases) or len(lean) != len(cases):
        raise RuntimeError(f"Expected {len(cases)} results, got {len(cpp)} C++ and {len(lean)} Lean")
    mismatches = 0
    for index, (case, reference, computed) in enumerate(zip(cases, cpp, lean), 1):
        if reference != computed:
            print(f"Mismatch {index} {case} gives C++ {reference} and Lean {computed}")
            mismatches += 1
    print(f"{len(cases)} cases, {mismatches} mismatches, seed {args.seed}")
    print(f"C++ {cpp_time:.3f} s, Lean {lean_time:.3f} s")
    return int(mismatches > 0)


if __name__ == "__main__":
    raise SystemExit(main())
