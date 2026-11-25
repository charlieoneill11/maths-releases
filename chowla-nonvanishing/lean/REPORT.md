# Chowla Lean report

`Chowla.certificate` proves Proposition 32's strict numerical consequence
for the explicit real model. `Chowla.main_of` and `Chowla.main_class_of`
prove the eventual nonvanishing lower bound over all discriminants and in
each of the six classes under the inputs listed below.

## Statement review

The four files for review are [Statement.lean](Chowla/Statement.lean),
[Certificate.lean](Chowla/Certificate.lean), [Cited.lean](Chowla/Cited.lean), and
[Claims.lean](Chowla/Claims.lean). The propositions `CertificateStatement`,
`MainStatement`, and `ClassStatement` specify the targets independently of
their proofs. [BLUEPRINT.md](BLUEPRINT.md) maps the paper to the Lean interfaces.
Charlie approved the four files for freezing at commit `23af00f` in
[draft PR #65](https://github.com/charlieoneill11/maths/pull/65).

The finite counts take a real cutoff by flooring it to an integer. The
quadratic L-function uses Mathlib's analytic continuation at every nonzero
modulus. It is total on integers for use in filters, with a constant value at
modulus zero. A zero is represented by a complex point in the open critical
strip and a multiplicity index. The enumeration retains the complex point and
uses its imaginary part in the statistic. GRH identifies that point with
`1/2 + iγ`. In particular, using multiplicity indices avoids applying a finite
order conversion that would turn an infinite order into zero.

The model uses Fourier profiles as generator indices. The underlying polynomial
type allows a generator at any real function. The model identities use the
generators in §4.1, given by bounded, measurable, even, compactly supported
profiles continuous at zero. The Fourier profiles of the products in the
inner products are the paper's convolutions. Lemmas on which this representation
depends, including symmetry and the monomial identity, belong to the model proof.

## Sources and toolchain

- Paper, appendix tables and oracle programs come from release commit
  [`cb8d8ff17702270e77d649c45ea473d45e19524d`](https://github.com/charlieoneill11/maths-releases/tree/cb8d8ff17702270e77d649c45ea473d45e19524d/chowla-nonvanishing).
- The original RH source pins Lean v4.33.1 and Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`. I checked both files at the
  original submission revision. The community mirror's current branch at
  `9282d3a102c4aff0e6026746db2a8990f5d9cddd` pins Lean v4.37.0-rc1 and
  Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`.
  [Original submission](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)
- The published original cache contains about 99.3 GB of extracted Lean
  artifacts. The workspace had about 60.7 GB free when checked, with four
  effective CPU cores and a 16 GiB memory limit. The original source build
  took multiple hours on the upstream high-memory host. We use the
  seven-cycle fallback and take GRH as an explicit hypothesis with the
  original `Statements.lean` proposition. A local axiom check on the RH
  theorem awaits a host that can import it.
  [Cache measurements](https://github.com/leanprover-community/riemann-hypothesis/blob/f28a764e76a18f68680446bf09682c24d1a8b5c4/verification/CACHE.md)
  [Original verification notes](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/774b9e8022f50d20be861ecc9d609cfc26436a81/verification/NOTES.md)
- This project pins Lean v4.29.1 and Mathlib
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. The Lake manifest pins its
  transitive dependencies.

## Hypotheses for milestone 2

The cited root number and zero-count fields use the versions needed for
fundamental discriminants of absolute value greater than one. Mathlib supplies
a functional equation with a root number and the analytic order. The sign
evaluation and the zero-count estimate remain cited inputs.

```lean
rootNumberOne : ∀ d : ℤ, IsFundDisc d → 1 < |d| → ∀ s : ℂ, completed d s = completed d (1 - s)
zeroCount : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℤ), IsFundDisc d → 1 < |d| → ∀ T : ℝ, 0 ≤ T →
  (zerosInBand d T).Finite ∧
    ((zerosInBand d T).ncard : ℝ) ≤ C * Real.log ((d.natAbs : ℝ) * (T + 2))
```

`rootNumberOne` is Davenport, *Multiplicative Number Theory*, chapters 2, 6
and 9. `zeroCount` is Davenport, chapter 16. The finite-set conjunct makes
the cardinality bound meaningful for an arbitrary set of indices.

```lean
emptyPatternMoments :
  ∀ (D : DiscClass) (W : ShellWeight) (k : ℕ) (_ : 0 < k) (f : Fin k → MomentTest),
    (∑ i, radius (f i).profile) < 2 →
    Tendsto
      (fun X : ℝ => weightedAverage D W X
        (fun d => ∏ i, zeroStatistic (fun x => (f i).toSchwartz x) d X))
      atTop (𝓝 (modelMoment fun i => (f i).profile))
```

This is Theorem 7 of the paper with the empty pattern. Its source is §3 and
the proof there uses GRH. The ordinate scale is `log X / (2π)`, the weight is
`W(m(d)/X)`, and `m(d)=|d|/κ`. Absolute convergence is a separate proof
obligation from the cited zero count. The arithmetic claim concerns the
admissible smooth test functions, while the certificate uses the bounded
profiles after smoothing is removed.

## Build and axiom audit

```sh
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe cache get
lake build
lake env lean -DautoImplicit=false Blueprint.lean
python3 scripts/check_axioms.py
```

The statement checkpoint built locally from restored Mathlib artifacts in
25.9 s. The first draft passed the two clean GitHub Actions builds in 4 min
31 s and 4 min 38 s. The analytic integration passed in 7 min 24 s and 7 min
32 s. The checkpoint through stage five passed in 9 min 49 s and 9 min 40 s.
The GitHub Actions times include dependency setup and the axiom audit.
The final local `lake build` with the 41 compiler-backed checks already
cached took 27.713 s, including compilation of the certificate and main
theorems. The final standalone blueprint also passed.

The audit checks the model, character, variational, counting and executable
soundness results. The standard allowlist is `propext`, `Classical.choice`
and `Quot.sound`. The compiler-backed facts have the separately listed
dependencies below.

## Data comparisons

The importer emits the rational rows from the programs and a second module
from the TeX independently. The equalities use `decide +kernel`. The programs
split (R0) into two rows with empty width lists. The Lean amplitude combines
their disjoint coefficient vectors to match the paper's single row. The
stage-one evaluator uses the released split when it rounds the Gram entries.
`Model/RowRefinement.lean` proves that the central product and Gram square
are preserved, including after the inherited rows are rescaled.

| Paper rows | Rows compared | Result |
| --- | ---: | --- |
| (R0), deterministic | 1 | Equal |
| (R1), printed higher modes | 9 | Equal |
| (R2), quadratic | 47 | Equal |
| (R3), cubic | 14 | Equal |
| (R4), quartic | 6 | Equal |
| (R5), quintic | 6 | Equal |
| (R6), sextic and septic | 9 | Equal |
| (R7), four or eight widths | 13 | Equal |
| (R8), mixed widths | 103 | Equal |
| (R9), three widths | 26 | Equal |

The independent Lean spreading recurrence checked all 639 fine-grid rows
in 34.4 s using the kernel.

| Regression comparison | Exact result | Lean | Python |
| --- | --- | ---: | ---: |
| 90 sampled Gram entries and 19 central enclosures, rational evaluator | Equal | 279.655 s | 3.277 s |
| The same 109 quantities, integer-grid evaluator | Equal | 120.647 s | 3.277 s |
| 208 published octic cross-check entries | Equal | 52.225 s | 114.071 s |
| 208 published entries after the cached optimization | Equal | 62.083 s | 85.782 s |
| 4,287 published Gram entries | Equal | 105.358 s | 48.534 s |
| 3,000 seeded Gram entries | Equal | 55.700 s | 26.935 s |

An initial stage-one bytecode run matched both central bounds in 33.661 s.
The two-row rounding sample also matched. The 2,388-entry block for
stage-one rows 40–63 matched the rounded sum `24848913723857691` in
79.272 s after preparation (39.343 s CPU for the whole command).
The optimized compiled probe of that block took 7.209 s. The 6,825-entry
late timing probe also matched in 24.228 s wall time and 12.792 s CPU.

To regenerate and repeat the comparisons, pass the pinned release's
`chowla-nonvanishing` directory to the scripts below.

```sh
python3 scripts/import_rows.py /path/to/release/chowla-nonvanishing
python3 scripts/compare_exact.py /path/to/release/chowla-nonvanishing
python3 scripts/compare_stages.py /path/to/release/chowla-nonvanishing
```

## Theorem 7 follow-up

A formal proof would need the explicit formula with the paper's conductor and
Fourier normalisations, squarefree and character averages in progressions,
GRH prime-sum estimates, low-frequency and bounded-moment estimates, the
distinct-prime reduction, quadratic Poisson summation, the smoothed transition
kernel, and reassembly as restricted cumulants. The existing Mathlib
L-function, character, Fourier and algebra infrastructure gives a starting
point. The proof would likely span several thousand lines across analytic
number theory and analytic estimates modules before prescribed patterns.
Uniform control in the pattern and the five additional classes are distinct
obligations beyond the base conductor-eight computation.

## Proved reductions

The model proof establishes Lemmas 6 and 21, centring, the connected
partitions and the Wick contraction over labelled partial matchings. The
grouping proof counts the labelled matchings between equal widths. Lemmas
27–28 give the rational truncated-power spline evaluator, including the
normalized primitives, the signed shift and convolution. Lemmas 29–31
justify the use of the rational spline for the extremal profile and the
rational cotangent bound. The packed integer-grid representation reduces to
the rational evaluator, with the direct rational fallback also covered.

The real Gram bridge uses those reductions to identify a packed evaluation
with the paper's model inner product. The central bridge applies Corollary 26
with the rational approximation error. `StageEvaluation.lean` proves
soundness of the eight stages on the real amplitude and `stageCheck_sound`
passes soundness from one accepted stage to the next.

The character checks include dyadic values, primitivity and even order at the
centre. Theorem 22 proves the variational inequality by smoothing and removing
the smoothing with the model continuity estimate. The proof of Lemma 8 uses
the square-divisor Möbius identity, evaluates the odd Möbius series as
8/π² from the trivial character modulo two and ζ(2), and uses partial
summation for the smooth mass. The dyadic shell argument gives the sharp
count in each class and the six classes combine to give the aggregate result.

## Exact stage checks

For stages 1–4 the numerical regression compares the lower and upper central
bounds, the Gram upper bound and the resulting rational proportion. For
stages 5–8 it compares the running rational lower bound.

| Stage | Results compared | Exact comparison | Compiled Lean arithmetic | Python oracle |
| --- | --- | --- | ---: | ---: |
| 1 | Both central endpoints, Gram upper bound, proportion | Equal | 376.648 s | Full stage-one oracle |
| 2 | Both central endpoints, Gram upper bound, proportion | Equal | 34.034 s | 130.885 s |
| 3 | Both central endpoints, Gram upper bound, proportion | Equal | 10.990 s | 59.773 s |
| 4 | Both central endpoints, Gram upper bound, proportion | Equal | 41.444 s | 302.643 s |
| 5 | Running lower bound | Equal | 44.066 s | Included in the 391.283 s resumed run through stages 4–5 |
| 6 | Running lower bound | Equal | 181.454 s over four Gram blocks | Released octic checkpoint |
| 7 | Running lower bound | Equal | 383.838 s over eight Gram blocks | Released octic checkpoint and 162.199 s parallel replay |
| 8 | Running lower bound | Equal | 310.111 s over four Gram blocks | 315.221 s cumulative parallel replay from stage six, plus a separate 329.416 s replay of the last row increments |

The stage-one Gram bound is exactly `49449387821493670097/100000000`.
Its gain margin lies strictly between 6 × 10⁻¹⁵ and 7 × 10⁻¹⁵. The full
compilation probe used 310.892 s of CPU. The SHA-256 of its three canonical
`numerator/denominator` lines is
`1972290184324f0c7f3fbe589390587779a3973c1bd6d89e886f821978764916`.

The stage-three margin lies strictly between 3090840240253192756346342 and
3090840240253192756346343 times 10⁻⁴⁰. The stage-five margin is between
1.656 × 10⁻¹⁵ and 1.657 × 10⁻¹⁵. The stage-eight lower bound is approximately
0.945341989313383391, with exact excess strictly between 313 and 314
multiples of 10⁻¹².

The exact late-stage rationals are recorded in `Chowla/StageData/`.
The SHA-256 values below use a single canonical `numerator/denominator`
line with a final newline.

| Python result | SHA-256 |
| --- | --- |
| R₆ | `d3d402a8879b71ec7e877c155a6a30a3e3c4edc84771615c7aa53385a5c6a33c` |
| R₇ | `54773d3e9a8a9fd55f663d1f42feb6c5cde646c5ef30ad8afcae90333c92ff25` |
| R₈ | `03085e09b70aef1f4aa9150766f520b90074a71b3e5b19c5d5502e83d5cc8054` |

The environment restart interrupted the output of the first stage-six
advance. Re-running all four stage-six blocks recovered the exact value.
The independent full stage-seven and stage-eight probes reproduced the
increments from the block computations. The final records reapply those
increments to the complete stage-six rational.

## Compiler-backed checks

Each executable check in `Chowla/Native/` has a proved real interpretation.

- `stageOneCentralCheck_sound` gives the real central interval.
  `stageOneLinearBlockCheck_sound` and `stageOneQuadraticBlockCheck_sound`
  bound the real Gram sums by rounding upwards. `stageOneBounds_eq_report`
  adds the blocks and recovers the stated enclosure.
- `stageCheck_sound` uses the preceding real enclosure and strict comparison
  to prove the enclosure and comparison for the accepted next stage.
- `lateStageCentralCheck_sound` gives a real lower bound and
  `lateStageGramBlockCheck_sound` gives equality with the exact real Gram
  contributions. The reassembly in `lateStageBounds_eq_report` preserves
  the accumulated stage bound.

The times below are Lean's wall-clock interpretation times from the checked
builds. Several independent modules were running concurrently.

| Checked theorem in `Chowla.Native` | Lean file under `Chowla/Native` | Time |
| --- | --- | ---: |
| `stage1_central_checked` | `Stage1Central.lean` | 12.8 s |
| `stage1_linear_0_80_checked` | `Stage1LinearA.lean` | 77 s |
| `stage1_linear_80_120_checked` | `Stage1LinearA.lean` | 64.2 s |
| `stage1_linear_120_160_checked` | `Stage1LinearA.lean` | 52.6 s |
| `stage1_linear_160_200_checked` | `Stage1LinearA.lean` | 61.7 s |
| `stage1_linear_200_240_checked` | `Stage1LinearA.lean` | 76.5 s |
| `stage1_linear_240_280_checked` | `Stage1LinearA.lean` | 119 s |
| `stage1_linear_280_320_checked` | `Stage1LinearA.lean` | 100 s |
| `stage1_linear_320_360_checked` | `Stage1LinearA.lean` | 120 s |
| `stage1_linear_360_400_checked` | `Stage1LinearB.lean` | 82.2 s |
| `stage1_linear_400_440_checked` | `Stage1LinearB.lean` | 73.3 s |
| `stage1_linear_440_480_checked` | `Stage1LinearB.lean` | 170 s |
| `stage1_linear_480_520_checked` | `Stage1LinearB.lean` | 173 s |
| `stage1_linear_520_560_checked` | `Stage1LinearB.lean` | 192 s |
| `stage1_linear_560_600_checked` | `Stage1LinearB.lean` | 129 s |
| `stage1_linear_600_640_checked` | `Stage1LinearB.lean` | 142 s |
| `stage1_linear_640_650_checked` | `Stage1LinearB.lean` | 38.3 s |
| `stage1_quadratic_checked` | `Stage1Quadratic.lean` | 31.7 s |
| `stage2_checked` | `Stage2.lean` | 103 s |
| `stage3_checked` | `Stage3.lean` | 49.8 s |
| `stage4_checked` | `Stage4.lean` | 287 s |
| `stage5_checked` | `Stage5.lean` | 192 s |
| `stage6_central_checked` | `Stage6.lean` | 187 ms |
| `stage6_gram_0_5_checked` | `Stage6.lean` | 184 s |
| `stage6_gram_5_8_checked` | `Stage6.lean` | 132 s |
| `stage6_gram_8_10_checked` | `Stage6.lean` | 37.8 s |
| `stage6_gram_10_13_checked` | `Stage6.lean` | 88.2 s |
| `stage7_central_checked` | `Stage7.lean` | 1.23 s |
| `stage7_gram_0_10_checked` | `Stage7.lean` | 53.3 s |
| `stage7_gram_10_20_checked` | `Stage7.lean` | 55.8 s |
| `stage7_gram_20_35_checked` | `Stage7.lean` | 113 s |
| `stage7_gram_35_50_checked` | `Stage7.lean` | 143 s |
| `stage7_gram_50_65_checked` | `Stage7.lean` | 103 s |
| `stage7_gram_65_80_checked` | `Stage7.lean` | 87.4 s |
| `stage7_gram_80_95_checked` | `Stage7.lean` | 95.2 s |
| `stage7_gram_95_103_checked` | `Stage7.lean` | 45 s |
| `stage8_central_checked` | `Stage8.lean` | 405 ms |
| `stage8_gram_0_6_checked` | `Stage8.lean` | 113 s |
| `stage8_gram_6_12_checked` | `Stage8.lean` | 97.1 s |
| `stage8_gram_12_18_checked` | `Stage8.lean` | 156 s |
| `stage8_gram_18_26_checked` | `Stage8.lean` | 117 s |

Lean v4.29.1 gives each successful `native_decide` invocation a generated
compiler axiom. The allowlist records the exact checked declaration names and
accepts each generated name only for its fact and the designated assembly
theorems. For example, `#print axioms Chowla.Native.stage3_checked` reports
`propext`, `Classical.choice`, `Quot.sound`, and
`Chowla.Native.stage3_checked._native.native_decide.ax_1_1`.

## Final axiom output

`scripts/check_axioms.py` passed for the complete library, including all
41 individually allowlisted compiler checks. The longest individual
compiler interpretation took 287 s. The following is Lean's output for
the certificate and aggregate theorem.

```text
'Chowla.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Chowla.Native.stage1_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_0_80_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_120_160_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_160_200_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_200_240_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_240_280_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_280_320_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_320_360_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_360_400_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_400_440_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_440_480_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_480_520_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_520_560_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_560_600_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_600_640_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_640_650_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_80_120_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_quadratic_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage2_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage3_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage4_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage5_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_0_5_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_10_13_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_5_8_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_8_10_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_0_10_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_10_20_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_20_35_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_35_50_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_50_65_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_65_80_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_80_95_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_95_103_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_0_6_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_12_18_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_18_26_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_6_12_checked._native.native_decide.ax_1_1]

'Chowla.main_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Chowla.Native.stage1_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_0_80_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_120_160_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_160_200_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_200_240_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_240_280_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_280_320_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_320_360_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_360_400_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_400_440_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_440_480_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_480_520_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_520_560_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_560_600_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_600_640_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_640_650_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_linear_80_120_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage1_quadratic_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage2_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage3_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage4_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage5_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_0_5_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_10_13_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_5_8_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage6_gram_8_10_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_0_10_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_10_20_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_20_35_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_35_50_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_50_65_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_65_80_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_80_95_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage7_gram_95_103_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_central_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_0_6_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_12_18_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_18_26_checked._native.native_decide.ax_1_1,
 Chowla.Native.stage8_gram_6_12_checked._native.native_decide.ax_1_1]
```

## Open problems

The frozen interfaces retain the quadratic root-number and local zero-count
facts from Davenport, the empty-pattern moment theorem from §3, and the
original GRH proposition. Importing the published GRH theorem requires a
compatible host and the axiom audit described above. The prescribed-pattern
moment theorem and two-moment ceiling are outside the scope of this
formalisation.

## Proof map

| Paper item | Lean declaration | Status |
| --- | --- | --- |
| Equation (1), Theorem 1 | `IsFundDisc`, `chi`, `DiscClass`, `InClass`, `discs`, `ClassStatement`, `MainStatement` | Done |
| Character and discriminant examples | `chi_neg_four`, `chi_eight`, nine `IsFundDisc` sanity lemmas | Done |
| General character properties | `chi_odd_prime`, `chi_two`, `chi_neg_one`, `chi_primitive` | Done |
| Lemma 4 | `even_central_order` | Done |
| §2.3 | `ZeroCopy`, `zeroSummand`, `zeroStatistic`, `zeroStatistic_summable` | Done |
| Definition 5 and equation (3) | `fourier`, `IsProfile`, `radius`, `oddProfile`, `delta`, `cumulant`, `modelMoment` | Done |
| Lemma 6(a–d) | `delta_eq_zero_of_support`, `abs_delta_le`, `delta_mul_delta_eq_zero`, `cumulant_continuity` | Done |
| Theorem 7, empty pattern | `PaperClaims.emptyPatternMoments` | Named hypothesis |
| Lemma 8, empty pattern | `squarefree_shell_mass`, `sharpShell_mass_deficit` | Done |
| §4.1 and equation (11) | `modelExpectation`, `centered`, `wick`, `modelExpectation_monomial`, `centered_moment` | Done |
| Definition 20 and equation (12) | `legendreProfile`, `Row.Admissible`, `IsAmplitude`, `amplitudeAt`, `H`, `G`, `inner_G`, `inner` | Done |
| Lemma 21 | `integral_H`, `extremal_cumulant` | Done |
| Theorem 22 | `smoothProfile_properties`, `pointwise_vanishing_bound`, `variational` | Done |
| Lemma 23 | `chain` | Done |
| Lemmas 24–25 | `connected_partitions`, `contraction_formula`, `equal_width_matching_count` | Done |
| Corollary 26 | `innerGRow_eq_cumulant` | Done |
| §7.1 and Lemma 27 | `integral_truncatedPower`, `convolution_truncatedPower`, `Spline.primitive_sound`, `Spline.convolution_sound`, `cumulant_covariance` | Done |
| Lemma 28 | `cumulant_shift`, `lowerPrimitive_oddProfile` | Done |
| Legendre profiles | `legendre`, `legendreProfile_integral`, `legendreProfile_bound` | Done |
| Lemmas 29–31 | `Hstar_pointwise_error`, `Hstar_integral_error`, `central_error`, `cot_upper` | Done |
| §8.1, amplitude data | `Rows`, `PaperRows`, `rows_r*_eq`, `r1Grid_agrees`, `F₈`, `final_amplitude_admissible` | Done |
| Proposition 32 | `StageBounds`, `early_stage_gain`, `late_stage_gain`, `certificate_stage` | Done |
| Milestone 1 | `CertificateStatement`, `certificate` | Done |
| §8, sharp count | `sharp_count_of_weighted`, `discs_partition` | Done |
| Milestone 2 | `main_class_of`, `main_of` | Done under the stated hypotheses |
