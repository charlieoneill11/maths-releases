# Sixth moment of the Riemann zeta function

**Result.** liminf M₆(T) / (c₃ T (log T)⁹) ≥ 41.6406…, where c₃ = a₃/9! and a₃ is the arithmetic factor; the conjecture of Conrey and Ghosh is M₆(T) ~ 42 c₃ T (log T)⁹, so every coefficient here is measured against the conjectured value 42. The previous record was 41.008. Enlarging the supports within the classes the paper uses (the proposition "Limit of the method": the dominant shapes, the extreme traces, the shapes with a short coordinate, and the balanced and mixed-row regions, with their reflections) cannot take the method beyond 41.94629 < 42; supports outside those classes are not covered by this ceiling.

**Hypotheses.** The proof uses Harper's bound ∫_T^{2T} |ζ(1/2+it)|⁶ dt ≪ T (log T)⁹, which rests on the Riemann hypothesis, now a theorem of Alpöge. The two-family optimum (41.2619…), the third-family bound and the ceiling use neither RH nor GRH. GRH for Dirichlet L-functions is not used. The mixed-row estimate uses the Kim–Sarnak bound and the Kuznetsov formula, both unconditional. The paper lists the dependence result by result after its table of results.

- Paper: [zeta-sixth-moment.pdf](zeta-sixth-moment.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs: [code/](code/). The paper cites them as `code/…`.
- Formal proof: [lean/](lean/). The masses μ(Ω) = 42 and μ(U₇) = C, the ceiling of Proposition 3, Lemma 90 and the deduction of Theorem 2 from the arithmetic pairings are checked in Lean 4 with Mathlib; see "Formal proof in Lean" below and Section 11 of the paper.

## Replaying the computations

You need Python 3.10 or later with NumPy, SciPy and SymPy. Run the scripts with assertions enabled (do not pass `-O`); each stops with an `AssertionError` if a check fails. Most checks are exact rational or symbolic identities. The exceptions are floating-point or sampled diagnostics, not certificates: `bridge_check.py` (a cubature comparison with tolerance 5·10⁻³), the numerical parts of `marked_spectral_checks.py` and `balanced_row_checks.py` (quadrature, and the ratio at two primes in section 3), and in `factorable_row_checks.py` the random test of the covering argument (section 3) and the numerical sums at p = 101 (section 4). The paper proves these statements; the diagnostics only test them. Run them from `code/`:

| Script | What it checks | Time |
| --- | --- | --- |
| `two_family_losses.py` | every number in the two-family optimum, 264076794201/6400000000 | 3 s |
| `optimization.py` | exact rational bounds for the Fraccaro test-function optimisation | 2 s |
| `verify.py` (reads `certificate.tsv`) | Fraccaro's 250 rows (41.00899…) and the 397-row certificate (41.02980…) | 10 s |
| `bridge_check.py` | the bridge lemma, by floating-point cubature at twelve certificate rows (largest relative numerator error 1.5·10⁻³, Gram discrepancy 5.5·10⁻⁴; threshold 5·10⁻³) | 2 s |
| `unequal_v_kernel_check.py` | the residue identity for unequal-length same-side tests | 3 s |
| `marked_spectral_checks.py` | the marked tests and the spectral estimate | 21 s |
| `balanced_row_checks.py` | the balanced row, sections 1–6 as cited in the paper; section 3 checks the first-order factorisation exactly | 35 s |
| `factorable_row_checks.py` | the factorable-moduli section, including the exact mass increment and C₆ = 41.6117… (the factorable stage; the final coefficient is checked by `mixed_row_checks.py`); section 3 reports how many of the 200,000 random draws pass the selection guards (30,575) | 4 s |
| `factorable_polygon_check.py` | exact masses of the factorable windows, including the coefficient 41.6117… (the factorable stage; the final coefficient is checked by `mixed_row_checks.py`) | 1 s |
| `mixed_row_checks.py` (reads `mixed_row_certificates.json`) | the mixed-row section: the seven new cells and C = 41.6406… (two integrations), the 84+84+672+672+784 exact case certificates, the prose case analyses for ς < 1/8 (13,122 and 76,545 systems, 22 and 69 exact certificates), (C−2)/2, the ceiling with F⁺, the 44 affine identities of the section, and the coefficient 41.63737… without the represented level | 44 s |
| `trace_band_integrals.py` | the rational integrals for C₀ and for the ceiling before the mixed-row region F⁺ is added (41.946289153…; the increment from F⁺ is checked by `mixed_row_checks.py`); it also prints a legacy thin factorable window, labelled as such, which is not the paper's region | 1 s |
| `trace_band_geometry.py` | an independent rational triangulation of the same masses, including μ(E′) = 105/8 and C₀; it also prints coefficients of intermediate regions from earlier drafts (41.5921…, 41.5922…) and of the legacy thin factorable window (41.595846295…, labelled as superseded), none of which is the factorable stage checked by `factorable_polygon_check.py` or the release coefficient checked by `mixed_row_checks.py` | 1 s |

```sh
cd code
( for f in two_family_losses optimization verify bridge_check unequal_v_kernel_check \
           marked_spectral_checks balanced_row_checks factorable_row_checks \
           factorable_polygon_check mixed_row_checks trace_band_integrals trace_band_geometry; do
    python3 -B "$f.py" || exit $?
  done )
```

The subshell stops at the first failing script and exits with that script's nonzero status, so a shell script ending with this block reports the failure; it exits with status 0 only if all twelve scripts pass.

The times are from one core of a 2.1 GHz Xeon on 24 November 2026, when all twelve scripts passed (about 125 s in total). `marked_geometry.py` and `spread_geometry.py` are modules that the scripts import. `gen_certificates.py` regenerates `mixed_row_certificates.json` by floating-point linear programming with SciPy; it is not part of the check, and it overwrites `mixed_row_certificates.json` in the current directory.

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development, pinned to Lean v4.29.1 and Mathlib v4.29.1. It proves `mu_Omega : μ Ω = 42`, `mu_U7 : μ U7 = ENNReal.ofReal C`, the exact ceiling of Proposition 3 (`mu_ceiling`, `ceilingMass_lt`, `projection_ceiling_exact`), and Lemma 90 with its covering corollary (`lemma90`, `lemma90_covering`). `main_of` proves Theorem 2, stated in [lean/ZetaSixth/Statement.lean](lean/ZetaSixth/Statement.lean) with Mathlib's `riemannZeta`, from `PaperPairings` ([lean/ZetaSixth/Claims.lean](lean/ZetaSixth/Claims.lean)): the existence of a faithful family whose closed span contains v·1_{U₇}, which is the conclusion of Theorem 79. The analytic theorems behind the pairings are not formalised.

- **What you trust.** Everything except Lemma 90 depends only on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with all arithmetic done in the kernel. `lemma90` and `lemma90_covering` also depend on 3 named checks of Farkas certificates imported from `code/mixed_row_certificates.json`. Each named check is a Boolean checker written in Lean, with a Lean proof of what a successful run means, and is evaluated with `native_decide`. Each such evaluation adds one compiler-generated axiom stating that the check evaluates to `true`, so you trust the Lean kernel plus the Lean compiler for those evaluations.

To replay, from `lean/`:

```sh
lake build --wfail
lake env lean Blueprint.lean
python3 scripts/check_axioms.py
```

A clean CI build took about six minutes. [lean/REPORT.md](lean/REPORT.md) gives the exact values, the timings and the axiom printout; [lean/BLUEPRINT.md](lean/BLUEPRINT.md) maps the paper's results to Lean declarations. REPORT.md was written in the development repository, so its links to pull requests and CI runs there do not resolve here. Its open item on §8.1 predates the source check of 24 November 2026; see the note at the end of that item.

## Citing

BibTeX (also in [CITATION.bib](CITATION.bib) and on the [paper's page](https://charlesponeill.com/maths-releases/zeta-sixth-moment/)):

```bibtex
@misc{zeta-sixth-moment-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra} and {Fable}},
  title        = {An improved lower bound for the sixth moment of the {R}iemann zeta function},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlesponeill.com/maths-releases/zeta-sixth-moment/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/zeta-sixth-moment}},
}
```
