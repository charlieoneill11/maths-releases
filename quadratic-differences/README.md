# Four-colour quadratic van der Waerden numbers

**Result.** For all integers e, f, not both zero, W(ex² + fx; 4) ≤ 57|e| + 39|f| + 1. Here W(P; 4) is the least N such that every four-colouring of {1, …, N} has two distinct integers of the same colour whose difference is P(d) for some integer d. So the optimal constant C₄ in W(ex² + fx; 4) ≤ C₄(|e| + |f|) + 1 is 57. Kumthekar, Gasarch, Regli and Whitehouse ([arXiv:2611.14913](https://arxiv.org/abs/2611.14913v1)) proved the bound with 64, showed 57 ≤ C₄ ≤ 64, and posed determining C₄ as an open problem. Both coefficients are attained: W(x²; 4) = 58 and W(x² + x; 4) = 97.

The paper also determines W(x² + jx; 4) for 0 ≤ j ≤ 8:

| j | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| W(x² + jx; 4) | 58 | 97 | 82 | 81 | 75 | 89 | 73 | 49 | 53 |

The values for j = 0, 1 and 7 were known; the other six are new.

- Paper: [quadratic-differences.pdf](quadratic-differences.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs, certificates and notes: [code/](code/). The research notes are [code/README.md](code/README.md) and [code/forcing.md](code/forcing.md).

## What the proof relies on

The proof is computer-assisted. Besides short arguments given in full in the paper, it uses four finite computations:

- an 8 × 16 periodic tile that four-colours the lattice graph on ℤ² with steps (d, ±d²), 1 ≤ d ≤ 7 (this can also be checked by hand);
- a SAT refutation showing that a 350-point subset of the rectangle [0, 10] × [0, 64] with the steps 1 ≤ d ≤ 8 is not four-colourable;
- a check that each of sixteen small configurations forces a periodic colour pattern on a block of 15 points;
- a SAT refutation showing that every proper four-colouring of the even points of a 12 × 58 rectangle contains one of these configurations.

Each SAT refutation has a DRAT proof checked by drat-trim, a separate proof checker. The upper bounds in the table are also DRAT-checked refutations, and the lower bounds are explicit colourings, printed in the paper's appendix.

## Checking the result

From `code/`, with Python 3.10 or newer and a C compiler:

```sh
cc -O2 drat-trim.c -o drat-trim
python3 verify.py ./drat-trim             # the nine thresholds, the tile and the rectangle sizes (2 s)
sh replay_forcing.sh ./drat-trim          # the 12 x 58 formula, its clause audit and the stored proof (40 s)
python3 cyclic_search.py 192              # the search for periodic colourings in the paper's remarks (75 s)
```

The 350-point refutation is re-solved rather than stored. Build Kissat 4.0.4 from its release tag `rel-4.0.4` (commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`), as [code/README.md](code/README.md) describes, then run

```sh
sh replay_grids.sh <kissat> ./drat-trim   # the even part of [0,10] x [0,64] and the 350-point subset (6 min)
```

[code/check_quadratic.py](code/check_quadratic.py) was written separately for the paper. It takes the colourings, the tile and the sixteen configurations from the paper, rebuilds every CNF formula from the definitions, compares each with the formula the folder's encoders produce, and runs drat-trim on the stored proofs against its own formulas. With Kissat it also re-solves the 350-point formula. It needs only the standard library and takes about three minutes:

```sh
python3 check_quadratic.py . ./drat-trim <kissat>
```

All of these passed on 25 November 2026. The SHA-256 hashes of the main formulas and proofs are listed in the paper's last section.

## Further notes

The notes [code/strip.md](code/strip.md) and [code/palette.md](code/palette.md) record further results that the paper does not use or check to the same standard, among them that the limiting worst ratio near the axis f = 0 is an integer between 52 and 57.

`drat-trim.c` is Marijn Heule's proof checker (MIT licence, copyright notice in the file), included so that the checks can be built from this folder.

## Citing

```bibtex
@misc{quadratic-differences-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra}},
  title        = {The optimal constant for four-colour quadratic van der {W}aerden numbers},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlieoneill11.github.io/maths-releases/quadratic-differences/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/quadratic-differences}},
}
```
