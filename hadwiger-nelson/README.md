# Unit-distance graphs and six colours

**Result.** Every unit-distance graph with at most 10,689 vertices, or at most 245,510 edges, is 6-colourable. Equivalently, a seven-chromatic unit-distance graph, if one exists, has at least 10,690 vertices and at least 245,511 edges; these are lower bounds, not the size of a known graph. The previous bounds, also inclusive, were 6,992 vertices, from the partial colouring of J. Parts ([arXiv:2010.12668](https://arxiv.org/abs/2010.12668)), and 232,645 edges, from the estimate of A. de Grey and J. Parts ([arXiv:2303.14714](https://arxiv.org/abs/2303.14714)) that a seven-chromatic unit-distance graph has at least 232,646 edges. De Grey and Parts describe their values as estimates obtained by numerical integration in Mathematica, and publish no interval certificate.

- Paper: [hadwiger-nelson.pdf](hadwiger-nelson.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs and data: [code/](code/). The appendix "Data and programs" of the paper describes each file.
- Formal proof: [lean/](lean/). The edge bound is proved in Lean 4 with Mathlib, and the vertex bound from four published facts about crossing numbers; see "Formal proof in Lean" below and Appendix B of the paper.

## Replaying the computations

You need Python 3.10 or later with NumPy and `python-flint` (for ball arithmetic), and `g++` with C++17 and 128-bit integers (the Python scripts call it to compile the two C++ files). Run from `code/`:

| Command | What it checks | Time |
| --- | --- | --- |
| `python3 cap22_finite_edge.py` | the wave theorem for W_E (quadrature) | 1–6 s |
| `python3 cap22_finite_star.py` | the star certificate and the edge bound 245,510 | 75–105 s |
| `python3 -S cap16_finite_switch.py` | the wave conditions (W1)–(W4) for W_V, including y₀ < H/4, and q and p for W_V with N = 2²⁶ | 1 min |
| `python3 -S cap22_point_parameters.py` | the constants of the certificate section | 12–30 s |
| `python3 -S cap22_partial_star.py` | β_V (compiles and runs `cap22_partial_star.cpp`) | 12–30 s |
| `python3 -S cap22_double_arcs.py` | the checks of the centres section | 2–7 s |
| `python3 -S cap22_point_combined.py` | both finite checks at n = 10,689, and the failures at n = 10,690, where this certificate stops | 15–30 s |

`cap22_point_crosscheck.py` is the second, separately written implementation of the finite check; `cap22_point_combined.py` runs both. The first program proves the stated upper bound 0.999999995095531514 for the final box bound at n = 10,689; the second checks only the weaker statement that the box bound is below 1, and shares with the first the routines for the centre credit and the close-pair counts. `cap22_point_combined.py` exits with an error unless both pass at n = 10,689, and `cap22_finite_star.py` exits with an error if the certified edge bound is below 245,510. `wave_independent.py` is a separate Python implementation of the integer routine in `cap14_global_angle.cpp`.

All seven commands were re-run from this folder on 24 November 2026, one after another, with Python 3.13 (assertions enabled), python-flint 0.9.0 and g++ 13.3 on a 2.1 GHz Xeon. Each exited with status 0, and its printed output was identical to the result recorded when the certificate was first computed; `cap22_point_parameters_result.json` and `cap22_partial_star_result.json` in this folder are two of these records. The longer times in the table are from running all seven at once. The other files in this folder are modules and data that these programs import.

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development, pinned to Lean v4.29.1 and Mathlib v4.29.1. [lean/HadwigerNelson/Statement.lean](lean/HadwigerNelson/Statement.lean) states

```lean
theorem edges_le_245510 (E : Finset (Plane × Plane)) (hE : ∀ e ∈ E, dist e.1 e.2 = 1)
    (hcard : E.card ≤ 245510) :
    ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2
theorem points_le_10689_of_cited (h : CitedFacts) (X : Finset Plane) (hX : X.card ≤ 10689) :
    ∃ c : Plane → Fin 6, ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y
```

where `Plane` is `EuclideanSpace ℝ (Fin 2)`. `CitedFacts`, in [lean/HadwigerNelson/Cited.lean](lean/HadwigerNelson/Cited.lean), holds the four published facts about crossing numbers and drawings used in Section 5 of the paper (Büngener–Kaufmann Theorem 4(b), Büngener–Franz–Kaufmann–Pfister Theorem 7, and two properties of drawings from Schaefer's survey). The edge theorem does not use them.

- **Route.** The Lean proof replaces the height quadrature by the angular-bin bound of Proposition 12 at 2²⁸ bins, which gives the weaker constant 4077152·10⁻¹² in place of p_E; this still gives 245,510 edges. It also uses the pointwise packing bound (Lemma 31) in place of Lemma 32. Appendix B of the paper describes both changes.
- **What you trust.** `edges_le_245510` depends on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on 8 named checks; `points_le_10689_of_cited` on the same axioms and 17 other checks. Each named check is a Boolean checker written in Lean, with a Lean proof of what a successful run means, and is evaluated with `native_decide`. Each such evaluation adds one compiler-generated axiom stating that the check evaluates to `true`, so you trust the Lean kernel plus the Lean compiler for those evaluations.

To replay, from `lean/`:

```sh
lake build
lake env lean scripts/axioms.lean > axioms.log
python3 scripts/check_axioms.py axioms.log
```

A clean build with cached Mathlib artifacts took about 14 minutes. [lean/REPORT.md](lean/REPORT.md) gives the time of every check, the full axiom printout and the comparisons with the programs in `code/`; [lean/BLUEPRINT.md](lean/BLUEPRINT.md) maps the paper's results to Lean declarations. REPORT.md was written in the development repository, so its links to pull requests and CI runs there do not resolve here.

## Citing

BibTeX (also in [CITATION.bib](CITATION.bib) and on the [paper's page](https://charlesponeill.com/maths-releases/hadwiger-nelson/)):

```bibtex
@misc{hadwiger-nelson-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra} and {Fable}},
  title        = {Six colours suffice for every unit-distance graph with at most 10{,}689 vertices or 245{,}510 edges},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlesponeill.com/maths-releases/hadwiger-nelson/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/hadwiger-nelson}},
}
```
