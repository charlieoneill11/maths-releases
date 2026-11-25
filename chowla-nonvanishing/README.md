# Central values of quadratic Dirichlet L-functions

**Result.** L(1/2, χ_d) ≠ 0 for more than 94.53419890% of fundamental discriminants d, counted by |d| ≤ X, in the sense of the lower limit as X → ∞. The bound holds separately in each of the six classes of d given by its sign and 2-adic type. The previous proportion was 94.2730%, from the one-level density with Fourier support in (−2, 2).

**Assumptions.** The proportion uses GRH for Dirichlet L-functions, which Alpöge has proved (reference [Alpoge] in the paper), so it is unconditional. The paper states where GRH enters. Its last theorem, the two-moment ceiling for multipliers that depend only on the symbols χ_8m(p) at the odd primes p ≤ y, uses neither the Riemann hypothesis nor GRH.

**Rounding.** The certified constant is the rational number p* = 0.9453419890. The exact value reached by the last stage is 0.94534198931…, so the bound may not be rounded up: "more than 94.5342%" is not certified.

- Paper: [chowla-nonvanishing.pdf](chowla-nonvanishing.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs: [code/](code/). Appendix A of the paper describes them and lists their SHA-256 digests.
- Formal proof: [lean/](lean/). The certificate of Proposition 32 is proved in Lean 4 with Mathlib, and Theorem 1 from GRH, two classical facts and Theorem 7 with the empty pattern; see "Formal proof in Lean" below and Appendix B of the paper.

## Replaying the certificate

You need Python 3.9 or later and nothing else. The programs use `functools.cache` and `math.lcm`, which Python 3.8 lacks, and otherwise only exact integer and rational arithmetic from the standard library. Run the eight stages in order from `code/`. Each asserts its exact inequality and then prints the proportion it certifies:

| Command | Stage | Prints a proportion above | Time |
| --- | --- | --- | --- |
| `python3 -B chowla_subgrid_single_certificate.py` | 1 | 0.94531427448210 | 1.5 min (uses 4 cores) |
| `python3 -B chowla_cubic_single_certificate.py` | 2 | 0.945321516147 | 40 s |
| `python3 -B chowla_quartic_single_certificate.py` | 3 | 0.945325433280444 | 20 s |
| `python3 -B chowla_one_exception_certificate.py` | 4 | 0.945325784098260 | 1.5 min |
| `python3 -B chowla_sextic_septic_certificate.py` | 5 | 0.94532732177059 | 45 s |
| `python3 -B chowla_octic_certificate.py` | 6 | 0.9453286989000 | 2.5 min |
| `python3 -B chowla_mixed_width_certificate.py` | 6–7 | 0.9453391726 | 5.5 min |
| `python3 -B chowla_three_width_certificate.py` | 6–8 | 0.9453419890 | 8 min |

Stages 6–8 start from the rational number produced by stage 5. The last line, `Verified lower limiting nonvanishing proportion above 0.9453419890.`, is the bound in the main theorem. The remaining certificate files are modules: `chowla_grid160_certificate.py` and `chowla_spectral_refinement_certificate.py` hold the rows used in stage 1, `chowla_joint_certificate.py` is the rational spline arithmetic, and `chowla_quadratic_certificate.py` holds the cumulant and its internal checks.

## Cross-checks

Stages 2 and 3 compute Gram entries by enumerating partitions; stages 4–8 enumerate matchings. Two programs recompute Gram entries by the other method and assert exact agreement:

| Command | Recomputes | Time |
| --- | --- | --- |
| `python3 -B chowla_octic_crosscheck.py` | all 208 entries between a stage-6 row and a stage-5 or stage-6 row, by partitions | 35 s |
| `python3 -B chowla_matching_crosscheck.py` | all 4,287 stage-3 entries by matchings; by partitions, all 8,385 entries among the stage-7 and stage-8 rows, all 2,838 entries between those rows and the stage-5 and stage-6 rows, and 3,000 entries between those rows and the rows of stages 1–4, chosen with a fixed seed | 3.5 min |

Both methods call the same routine for the individual cumulants, so these checks do not replace an independent implementation.

All stages and both cross-checks were re-run from this folder on 24 November 2026 with Python 3.13 and passed; stages 3 and 4 also pass with Python 3.9. Times are wall-clock times on a shared 2.1 GHz Xeon, one core except where noted.

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development, pinned to Lean v4.29.1 and Mathlib v4.29.1. `Chowla.certificate`, stated in [lean/Chowla/Certificate.lean](lean/Chowla/Certificate.lean), proves

```lean
0.9453419890 < (19 - Real.cot (1 / 4)) / 16 + inner_G F₈ - inner F₈ F₈ / 2
```

for the model inner products of the paper, with no hypothesis. `Chowla.main_of` and `Chowla.main_class_of` prove Theorem 1, stated in [lean/Chowla/Statement.lean](lean/Chowla/Statement.lean), for all discriminants and in each of the six classes, from three hypotheses: GRH for Dirichlet L-functions (`DirichletLZerosOnLine`, the statement of the formal GRH proof, which uses a later Lean and Mathlib and so is not imported); `CitedFacts` (root number 1 and a zero count, from Davenport); and `PaperClaims` (Theorem 7 with the empty pattern). Theorems 2 and 3 are not formalised.

- **What you trust.** All three theorems depend on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on 41 named checks, which evaluate the eight stages of Proposition 32. Each named check is a Boolean checker written in Lean, with a Lean proof of what a successful run means, and is evaluated with `native_decide`. Each such evaluation adds one compiler-generated axiom stating that the check evaluates to `true`, so you trust the Lean kernel plus the Lean compiler for those evaluations.
- **Cross-checks.** The rows (R0)–(R9) are imported both from the programs and from the paper's TeX, and Lean checks that they agree. Every stage agrees exactly with the programs in `code/`.

To replay, from `lean/`:

```sh
lake build
lake env lean -DautoImplicit=false Blueprint.lean
python3 scripts/check_axioms.py
```

A clean CI build took 23 minutes. [lean/REPORT.md](lean/REPORT.md) gives the time of every check, the axiom printout and the comparisons; [lean/BLUEPRINT.md](lean/BLUEPRINT.md) maps the paper's results to Lean declarations. REPORT.md was written in the development repository, so its links to pull requests and CI runs there do not resolve here.

## Citing

BibTeX (also in [CITATION.bib](CITATION.bib) and on the [paper's page](https://charlesponeill.com/maths-releases/chowla-nonvanishing/)):

```bibtex
@misc{chowla-nonvanishing-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra} and {Fable}},
  title        = {Central nonvanishing of quadratic {D}irichlet {$L$}-functions: beyond the one-level density bound, uniformly in local conditions},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlesponeill.com/maths-releases/chowla-nonvanishing/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/chowla-nonvanishing}},
}
```
