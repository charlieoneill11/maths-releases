# Packing cubes in odd tori

**Result.** For every N = 4m + 1 with m odd (N = 5, 13, 21, 29, …), the largest number of pairwise disjoint 2×2×2 cubes in the discrete torus (ℤ/Nℤ)³ is N(mN − 1)/2. Equivalently, α(C_N^⊠3) = N(mN − 1)/2 for every N ≡ 5 (mod 8). Baumert, McEliece, Rodemich, Rumsey, Stanley and Taylor gave this construction and conjectured that it is optimal in 1971. Bohman, Holzman and Natarajan proved it when N is prime and showed the maximum is at most two larger in general. Natarajan proved it when m is prime. The proof here is computer-assisted.

- Paper: [cube-packing.pdf](cube-packing.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs: [code/](code/). The paper's section "The computations" describes them.

## What the proof relies on

The proof uses the published lemmas of Bohman, Holzman and Natarajan (Electron. J. Combin. 20(3) (2013), #P10). It also uses results from the long version of their paper, which is available from Tom Bohman's web page and has not been published in refereed form:

- Theorem 22, which reduces a planar packing one point short of the maximum to a maximum packing of side N − 4, N or N + 4;
- Lemmas 12, 16, 19 and 23;
- the double-expansion case of Section 3.2.2.

The paper's Section 2 lists exactly what is used.

## Replaying the computations

From `code/`, run

```sh
sh replay.sh cutoff   # the 3,589 comparisons at 23 sides between 173 and 645
sh replay.sh 85
sh replay.sh 133
sh replay.sh 141
sh replay.sh 261
sh replay.sh 301
```

Each run prints its working directory and exits with status 0 if no configuration survives. It needs Python 3.10 or newer and a C++17 compiler. At 261 and 301 an independent check reads the recorded catalogue:

```sh
python3 check_homogeneous_lines.py 261 DIRECTORY/planes.bin
```

Here `DIRECTORY` is the directory printed by the replay.

| Side | Orbits | Survivors | Time on 25 Nov 2026 |
| ---: | ---: | ---: | ---: |
| 85 | 5,558 | 0 | about 4 min |
| 133 | 8,844 | 0 | about 4 min |
| 141 | 1,266 | 0 | 22 s |
| 261 | 114 | 0 | 7 s |
| 301 | 38 | 0 | 2 s |
| cutoff | 3,589 transitions | survivors 261 and 301 | 1 s |

All six runs and the independent check at 261 and 301 were replayed on 25 November 2026 and gave these results.

The options `205` and `1445` of `replay.sh`, and the programs `verify_1445.cpp`, `verify_85.py` and `small_orders.py`, check auxiliary results from the research draft that the paper does not use.

These programs were copied from `cube-packing/` on branch `codex/cube-packing-proof` (commit 31b7e9df) of the development repository.

## Citing

```bibtex
@misc{cube-packing-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra}},
  title        = {Packing side-two cubes in the three-dimensional torus of side {$N\equiv5\pmod 8$}},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlieoneill11.github.io/maths-releases/cube-packing/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/cube-packing}},
}
```
