# Sixth moment formalisation report

Lean proves the chamber mass `μ Ω = 42`, the exact mass `μ U7 = C`, the exact support ceiling, and Lemma 90 with its covering theorem. Theorem 2 is conditional on `PaperPairings`, the conclusion of the paper's analytic theorems. Charlie signed off on the four statement files at `8d334ad` and approved the smoothness correction at `2cc2271`. The four files are frozen with that correction.

## Sources and toolchain

| Item | Version |
| --- | --- |
| Paper and programs | `charlieoneill11/maths-releases` at `cb8d8ff17702270e77d649c45ea473d45e19524d` |
| Lean | v4.29.1, `f72c35b3f637c8c6571d353742168ab66cc22c00` |
| Mathlib | v4.29.1, `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| `mixed_row_checks.py` SHA-256 | `cc06eade53e493290bfbc01ef28bffac4a8293e2f372c94abc47fd6b51f45b16` |
| `mixed_row_certificates.json` SHA-256 | `d366474e8177fbc451cedb772574589ca09230599e5282b5c6145c0392844cf0` |

Both hashes match the computation paragraph in the proof of Theorem 79. [Paper and source scripts](https://github.com/charlieoneill11/maths-releases/tree/cb8d8ff17702270e77d649c45ea473d45e19524d/zeta-sixth-moment)

## Approved smoothness correction

The original `Weight.smooth` field used `(⊤ : WithTop ℕ∞)`, which Mathlib calls `ω`. At that order, a function on ℝ is real analytic. The support condition forced it to vanish on `(-∞,1)`, and the identity theorem forced it to vanish on all of ℝ. This contradicted `Weight.nonzero` and made the quantification over weights in `Faithful` vacuous. The approved one-line correction uses `((⊤ : ℕ∞) : WithTop ℕ∞)`, the order for infinite differentiability. [Corrected weight definition](ZetaSixth/Claims.lean#L14) · [Mathlib smoothness orders](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean#L111-L114) · [Identity theorem](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Analysis/Analytic/Uniqueness.lean#L204)

## Analytic hypothesis

```lean
structure PaperPairings : Prop where
  exists_faithful : ∃ 𝒯 : Family, Faithful 𝒯 ∧ InFamilySpan 𝒯 (U7.indicator v)
```

The structure records the conclusion of Theorem 79, which builds on Theorems 16, 23, 52 and 67. `Faithful` takes limits in `ℂ` for each allowed weight. Its limiting pairings are real, computed against ordinary chamber volume. The conjugated slots are `B` in the numerator and `B'` in the Gram pairing. The time normalization uses `a3`, while the region measure uses `9! v²` against the restricted volume. The span membership uses the almost-everywhere equivalence class of the indicator, with an actual `Lp` witness.

The paper invokes Fraccaro's moment formulas, the Kuznetsov formula and spectral large sieves, Kim–Sarnak, Deshouillers–Iwaniec, Lichtman, Drappeau, Pascadi, Heath-Brown, Fouvry–Kowalski–Michel, and Harper's RH-based sixth-moment bound. The Lean implication takes the single hypothesis displayed above. [Claims.lean](ZetaSixth/Claims.lean)

## Reference computations

The authors' Python replay passed, including every published certificate batch. The table records exact reference values. Lean verified the mass computations and the exponent covering. The exact computed values agree with the manuscript.

| Comparison | Result |
| --- | --- |
| Chamber mass | Equal to `42` |
| Short-cubic coefficient, reference transcription | Equal to `8263261393/200000000` |
| Marked complement mass | Equal to `209/1024` |
| Marked short-divisor coefficient | Equal to `42 − 209/512` |
| Balanced coefficient `C₀` | Equal to `2578241177999/61983140352` |
| Factorable coefficient `C₆`, reference transcription | Equal to `3307268442615739142376085993/79479266349492187500000000` |
| Full all-marks gain from the balanced coefficient `C₀` | Equal to `665446127419388501239/20001196861299515678208` |
| All-marks gain measured from the factorable coefficient `C₆` | `446342629649862612781335389271984203/25646981479481579590121601562500000000`, matching the printed prefix `0.017403320153…` |
| Two-mark gain | Equal to `1592111573351043355967/264644248141002375000000` |
| Table 1 total | Equal to `268755110285287452500182503673016801/49130135420790450741077959596000000000` |
| Mixed-row coefficient | Equal to `112666832560750258461501594014215737455802061/2705696476246250148185796472625838239963136` |
| Ceiling increment from the mixed-row support | Equal to `196813181035147418047099/474637777079666241191850000000` |
| Ceiling | Equal to `13860404849860091/330432202525696` |
| Lemma 90(iii) and the fallback | 84, 84, 672, 672 and 784 branches replayed in Python |
| Lemma 90(i)–(ii) | 13,122 and 76,545 branches replayed in Python |

The exact values for the seven cells include both reflected halves. Each checked value equals the Python result and has the prefix printed in Table 1.

| Cell | Exact mass from Python replay |
| --- | --- |
| 1 | `303738701961421013/375042298197600000000` |
| 2 | `548395255530367/2651124843250000000` |
| 3 | `9090045139845151219/3478806019312650000000` |
| 4 | `1550623666362676605/3200621415779366111104` |
| 5 | `5312876028742353/18185348953291852904` |
| 6 | `905664298883259/869958349249567424` |
| 7 | `33779/1475789056` |

## Affine transcription

The identifiers below are in `Exponents.Degrees`. The displayed coefficients, strict inequalities, and band endpoints were compared with the cited paper displays. A margin is positive when the corresponding estimate saves. The half factors in the two direct margins are cleared by multiplying the full inequality by two.

| Lean | Paper source |
| --- | --- |
| Fields `ς`, `mark`, `g`, `r`, `i`, `tail`, `dual`, `z`, `x`, `E`, `w` | Mark region after (48), Lemma 82, “Degrees,” “Reduction of the modulus,” and Lemma 87 |
| `sigma`, `lambda`, `tau` | “Degrees” immediately before Lemma 83 |
| `m`, `n`, `j`, `D` | Ordering and summing the four dual degrees, before Lemma 83 |
| `Admissible`, through `D = lambda + i` | Lemma 82, “Degrees,” and Lemma 83(i) |
| `a`, `b` | Lemma 85 |
| `Z`, `y`, `C`, and nonnegativity of `z`, `x`, `E`, `y`, with `E ≤ Z` and `E ≤ a` | “Reduction of the modulus,” between Lemmas 85 and 86 |
| `u`, `budget` | “Normalisation,” between Lemmas 85 and 86 |
| `markCap`, `InMarkRegion` | The `𝒫⁺*` display after (48) |
| `Trivial` | The two stated alternatives in Lemma 90 |
| `splitBudget`, `splitDegree`, `Unsigned` | “Degrees” and Lemma 84, final consequence |
| `c`, `d`, `R`, `N` | Display before Lemma 86 |
| `P0`, `P1`, `P2`, `P3`, `SpectralSquare` | Lemma 86, four displayed margins, prerequisite and final disjunction |
| `0 ≤ w`, `w ≤ C` and `w ≤ mark` in `Admissible` | Lemma 87, after the bijection |
| `directTerms`, in list order | Lemma 87, the first four, next two, and final term of `𝒦` |
| `directMargin`, `Direct`, `DirectWithGain` | Final comparison of Lemma 87, for each term in the maximum |
| `Reciprocal` | Lemma 88, both arguments of the minimum less `u` |
| `J`, `level`, `representedBase`, `exceptional`, `representedMargin`, `RepresentedLevel` | Lemma 89(i)–(ii), including the eight affine choices in (59) |
| `BandI`, `BandII`, `BandIII` | Lemma 90(i)–(iii) |
| `markCapDifference` | Comparison immediately following Lemma 90 |

Two comments in the frozen exponent statements contain stray control characters in the printed names `τ` and `ς`. The source mapping above identifies both displays. [Required saving](ZetaSixth/Exponents.lean#L40) · [Mark domain](ZetaSixth/Exponents.lean#L121)

## Build and proof status

Run `lake build --wfail`, then `lake env lean Blueprint.lean` and `python3 scripts/check_axioms.py` from this directory. The axiom audit checks the declarations listed in `scripts/axioms.lean` and discovers each native theorem separately. The native proof dependencies appear below.

GitHub Actions passed the clean library build, blueprint elaboration, and axiom audit at `7f36dfa`. On the runner, `lake build --wfail` took 5 minutes 47.200 seconds after restoring the pinned Mathlib dependencies and removing the project's build artifacts. The audit verified 113 declarations, including five native Boolean equalities. [Passing CI run](https://github.com/charlieoneill11/maths/actions/runs/45513912042/job/138868314987)

```text
'ZetaSixth.mu_Omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaSixth.mu_U7' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaSixth.mu_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaSixth.ceilingMass_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaSixth.main_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The statements use `ℝ × ℝ × ℝ` for points, represent masses in `ℝ≥0∞`, and cast the paper's rational targets exactly into that type. The Lean blueprint elaborates examples matching the completed proofs to their statements. [Blueprint and statuses](BLUEPRINT.md)

## Assembly components

Lean constructs an admissible smooth bump in `nonempty_weight`. `Weight.exists_integral_gt` constructs weights bounded by one with integral arbitrarily close to one. `Euler.lean` proves the Euler-factor formula and multipliability and positivity of the prime product. The dyadic transfer uses the convergence of each log ratio and the sum of finitely many dyadic lengths. [Checked weights](ZetaSixth/Weights.lean) · [Euler product](ZetaSixth/Euler.lean) · [Dyadic transfer](ZetaSixth/MomentWindows.lean)

Expanding the weighted square of the difference between the zeta expression and a test gives the lower bound `2 Re N − Re G` for the smoothed moment. The corresponding continuous quadratic functional on the closed profile span takes the value `‖P v‖²` at the orthogonal projection `P v` and `‖v · 1_U‖²` at the supported indicator. The square identity also covers zero-norm profiles. For the ceiling, restriction to the complement is a continuous linear map. Its kernel contains the closed profile span, so Cauchy–Schwarz bounds the squared projection norm by the mass of the support. [Pairing proof](ZetaSixth/PairingProofs.lean) · [Projection proof](ZetaSixth/Projection.lean) · [Conditional Theorem 2 and exact ceiling](ZetaSixth/Theorem2.lean)

## Verified polynomial integration

`SparsePoly.eval_integrate` proves the interval integral formula for rational sparse polynomials evaluated over the reals. `Cell.integral_eq` applies Fubini to strict nested cells with ordered affine faces and relates the real set integral to the computed rational mass. The proof of `mu_Omega` uses a single cell in the original coordinates and kernel reduction. The chamber reflection and the shear to `(x+y,x,z)` preserve ambient volume. Reflection also preserves `μ`. [Checked integration and chamber mass](https://github.com/charlieoneill11/maths/actions/runs/45509456607)

The support calculations subdivide `N0` into five short-sum cells and its balanced piece into eight. The mixed gain uses five all-marks cells, two two-mark cells, and the seven cells from Table 1. The ceiling calculation takes the low-trace half of `B` and reflects it across the center. That half has six cells. The balanced addition and the portion of the mixed addition outside it each have two cells. All chart cuts discard only affine boundaries proved null in `LinearBoundaries.lean`.

The chamber, `U7`, and ceiling calculations use standard Lean axioms and kernel arithmetic.

## Lemma 90 and the native checks

`ZetaSixth.Exponents.lemma90` proves the claims on the three ranges. Its corollary `lemma90_covering` applies at every point of the mark region. The proofs of parts (i) and (ii) use the paper's inequalities with the full range of `x`. Part (iii) uses exact nonnegative rational multipliers. The checker establishes contradiction for real assignments satisfying a verified branch with positive cap slack. The importer checks both released source digests and reproduces the certificate data byte for byte. `ExponentProofs/Identities.lean` checks all 44 released affine identities and the slope equality by kernel proofs. [Covering proof](ZetaSixth/ExponentProofs/Covering.lean) · [Checker soundness](ZetaSixth/ExponentProofs/Farkas.lean) · [Importer](scripts/import_exponent_certificates.py)

All five native checks are in `ZetaSixth/Native/ExponentCertificates.lean`. Their propositions have the form `Farkas.checkEncoded slack systems certificates = true`. `Farkas.checkEncoded_sound` yields the contradiction for a real assignment in any certified branch. A kernel reduction probe for the smallest batch did not reduce the checker's Boolean equality. The measurements below are local profiled interpreter times. The complete profiled command took 17.909 seconds, including imports and profiler output.

| Native theorem under `ZetaSixth.Exponents.NativeCertificates` | Branches | Profiled time |
| --- | ---: | ---: |
| `completionLow` | 84 | 0.368 s |
| `completionHigh` | 84 | 0.448 s |
| `representedLow` | 672 | 3.23 s |
| `representedMiddle` | 672 | 1.92 s |
| `representedHigh` | 784 | 1.92 s |

The axiom output for `lemma90` and `lemma90_covering` is identical apart from the theorem name.

```text
'ZetaSixth.Exponents.lemma90' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ZetaSixth.Exponents.NativeCertificates.representedHigh._native.native_decide.ax_1_1,
 ZetaSixth.Exponents.NativeCertificates.representedLow._native.native_decide.ax_1_1,
 ZetaSixth.Exponents.NativeCertificates.representedMiddle._native.native_decide.ax_1_1]
```

## Open problems

- The four estimates in §8.1 remain unchecked against their published statements (Deshouillers–Iwaniec Theorem 12, Lichtman Lemma 7.5, Drappeau Theorem 2.1, and Pascadi Lemmas 3.9–3.10). The paper's analytic argument remains represented by `PaperPairings`.
  *Note added in the release copy (24 November 2026):* after this report was written, the quoted estimates of §8.1 were compared with Lichtman's Lemma 7.5 and Drappeau's Theorem 2.1 (arXiv versions) and with Pascadi's Lemma 3.9 and Corollary 3.10 (journal version), and §8.1 of the paper ("Quoted estimates") now cites them in that form. Deshouillers–Iwaniec (1982) itself was not read. The formal development is unaffected, since these estimates enter only through `PaperPairings`.
- Optional Z4, the conditional formalisation of Theorem 1 for Fraccaro's two families, is deferred.
