"""Regenerate the interval certificates using python-sat==1.9.dev25 (Glucose 4.1)."""

import gzip
import json
from pathlib import Path

from pysat.solvers import Glucose4

from encode import clauses, interval


ROOT = Path(__file__).resolve().parent
THRESHOLDS = (58, 97, 82, 81, 75, 89, 73, 49, 53)


def main():
    rows = []
    for j, w in enumerate(THRESHOLDS):
        with Glucose4(bootstrap_with=clauses(*interval(j, w - 1))) as solver:
            if not solver.solve():
                raise RuntimeError(f"missing colouring for j={j}")
            word = "".join(str((v - 1) % 4) for v in solver.get_model() if v > 0)
        rows.append({"j": j, "W": w, "colouring": word})
        with Glucose4(bootstrap_with=clauses(*interval(j, w)), with_proof=True) as solver:
            if solver.solve():
                raise RuntimeError(f"claimed threshold for j={j} is colourable")
            proof = "\n".join(solver.get_proof()) + "\n"
        path = ROOT / "certificates" / f"j{j}.drat.gz"
        path.write_bytes(gzip.compress(proof.encode("ascii"), mtime=0))
    (ROOT / "thresholds.json").write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
