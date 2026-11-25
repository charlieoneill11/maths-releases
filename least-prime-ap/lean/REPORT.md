# Least-prime and divisor-density formalisation

The final targets in `LeastPrime/Statement.lean` and the two external inputs in
`LeastPrime/Cited.lean` were approved at `16a7bc4`. The blueprint maps the paper's proof to Lean
declarations. [Blueprint](BLUEPRINT.md) ·
[Release paper](https://github.com/charlieoneill11/maths-releases/blob/cb8d8ff17702270e77d649c45ea473d45e19524d/least-prime-ap/paper/main.tex)

## Toolchain

Lean v4.29.1, commit `f72c35b3f637c8c6571d353742168ab66cc22c00`. Mathlib v4.29.1, commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`. The Lake manifest pins the transitive dependencies.

`lake build` from a fresh package directory with the pinned dependency cache took 11.129 seconds.
`python3 scripts/check_axioms.py` passed. All nine audited declarations reported exactly
`[propext, Classical.choice, Quot.sound]`.

The clean GitHub checkout of proof commit `2f65a5c` passed the build, blueprint check and axiom
audit. Setup, dependency caching and `lake build` took 26m26s in the Lean action step. The blueprint
and axiom step took another 43 seconds. The full job took 27m19s. [CI run](https://github.com/charlieoneill11/maths/actions/runs/45509015210)

## Statement review

- `Tout` uses `0.142857` as its left endpoint, as in Proposition 14 and the verifier. The
  pasted `0.142858` produces an asymmetric union. The paper's larger set contains the pasted
  set and `[1/7, 1/5]`, so the paper's upper bound implies the pasted one by monotonicity.
- The window-cardinality lemma assumes `0 ≤ Q`. For `Q < 0`, the pasted `window` definition
  contains `0`, while both truncated natural floors are zero.
- The three theorem targets in `Statement.lean` are propositions. The conditional proof of
  Theorem 1 will also give `C = 4` using `mainBound`.

### Maynard

The printed Corollary 1.4 uses `2/5 + 5η`, as in §2 of the release paper. The arXiv v1 exponent
is `2/5 + η`. The printed corollary requires `x > x₀(η, A)`. Its exceptional-set size has constant
one. Shrinking the upper limit on sufficiently small `η` permits `η ≤ η₀`. The field chooses
`A = 1`, keeps the strict threshold and uses `AllClassesBelow`.
For `x > x₀ ≥ 2`, the lower comparison for `π(x; q, a)` is strictly positive because there is
at least one prime up to `x` and `φ(q) > 0` for `q ≥ 1`. The `x₀ ≥ 2` constraint comes from enlarging
the threshold. The arXiv identifier in the pasted instructions refers to a different article.
[Published Corollary 1.4](https://ora.ox.ac.uk/objects/uuid:da3b7279-d413-4ab1-962e-afa5d67507c2/files/s6w924c97m) ·
[arXiv:2006.08250v1](https://arxiv.org/abs/2006.08250v1)

```lean
maynard : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
  ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ < x → ∃ bad : Finset ℕ,
    (∀ q ∈ bad, 1 ≤ q ∧ (q : ℝ) ≤ x ^ (1 / 2 + η)) ∧
    (bad.card : ℝ) ≤ x ^ (1 / 2 + η) / Real.log x ∧
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ x ^ (1 / 2 + η) → q ∉ bad →
      (∃ d ∈ q.divisors, x ^ (2 / 5 + 5 * η) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x ^ (3 / 7 : ℝ)) →
      AllClassesBelow q x
```

### Donnelly–Grimmett

Theorem 1 treats logarithms divided by the log of the *remaining* integer and tends to the
product of independent uniforms. Corollary 2 treats logarithms divided by the log of the
*original* integer and tends to GEM(1). The field uses the finite-coordinate consequence of
Corollary 2, with `N` uniform on `1, …, X`, as in §3 of the release paper. The conditional choice
in (2.1) weights each prime value by its remaining multiplicity times its logarithm. Summing the
Lean weights over its remaining indices gives this choice. Corollary 2 pads with zeros, including
when `N = 1`. `averageLaw j 0` is extended by the zero vector since the limit uses `X → ∞`.
[Published article](https://doi.org/10.1112/jlms/s2-47.3.395) ·
[Scan transcription](https://www.academia.edu/27471392/On_the_Asymptotic_Distribution_of_Large_Prime_Factors)

```lean
donnellyGrimmett : ∀ j : ℕ, 0 < j → Tendsto (averageLaw j) atTop (𝓝 (stickProbability j))
```

## Proof status

| Paper | Lean declaration | Status |
| --- | --- | --- |
| Proposition 3 | `CitedFacts.maynard` | Approved hypothesis |
| Lemma 4 | `divisor_reduction` | Done |
| Theorem 5 | `CitedFacts.donnellyGrimmett` | Approved hypothesis |
| Lemma 6 | `divisor_of_revealed`, `revealed_of_divisor` | Done |
| Lemma 7 | `stickLaw_absolutelyContinuous`, `stickLaw_frontier_E_null`, `stickLaw_frontier_F_null` | Done |
| Proposition 8 | `eventually_density_lower`, `eventually_density_upper` | Done |
| Lemma 9 | `p_complement`, `q_complement` | Done |
| Lemma 10 | `p_recursion`, `q_recursion` | Done |
| Lemma 11 | `p_one_rescaled`, `q_one_rescaled`, `p_two`, `q_two` | Done |
| Lemma 12 | `cell_bounds` | Done |
| Lemma 13 | `hermite_hadamard_inv`, `hermite_hadamard_inv_nonpos`, `reciprocal_affine_decreasing_iff` | Done |
| Proposition 14 | `lowerP_sound`, `upperQ_sound`, `Checker.checkWindow_sound`, `p6_Tin`, `q5_Tout` | Done |
| §6 | `main_of_cited`, `density_lower_of_cited`, `density_upper_of_cited` | Done |

## Computation

The unmodified C++ reference had SHA-256
`83afd8be000a59fffffd3e648658e584fdec29924a9f2de9e2a0e37a01f131aa`.
Built with `c++ -O3 -std=c++17`, it printed `lower 587142/1000000`, `upper 595573/1000000`
and `PASS` in 31.820 seconds wall time. These are reference values. Lean checker outputs, the Table 1
runs and random-grid regression are described below. [Reference verifier](https://github.com/charlieoneill11/maths-releases/blob/cb8d8ff17702270e77d649c45ea473d45e19524d/least-prime-ap/code/verify_split_divisor_density.cpp)

The standalone compiled Lean evaluator returned `587142` and `595573` in 6m48.063s wall time.
The regression used seed `20261124` and compared 300 symmetric random grid sets at each level from
zero through six in each direction. It also tested six fixed edge cases through level three.
All 4,248 comparisons agreed. The C++ oracle took 11.201 seconds and the Lean evaluator took
215.734 seconds. The oracle wrapper uses the exact base formulas for levels zero and one and
extends the upper level-five cell count to level six for those comparisons. The random samples
use short gaps to keep the full cell schedules feasible at every depth.

### Proof implementation

- Lemma 7 uses the explicit triangular inverse and the null-image corollary of Mathlib's Jacobian
  theorem. The simplex frontier is included when bounding the event frontiers.
- Proposition 8 normalizes the difference of the two cumulative measure sums by `Q`.
  The normalized dyadic measure sum tends to half the corresponding probability, and the window
  cardinality divided by `Q` tends to `1/2`. This yields the eventual strict inequalities.
- Lemma 13 integrates tangent and secant bounds for the reciprocal function. The endpoint
  product comparison is proved equivalent to the sign test for the reciprocal coefficient.
- The checker uses `Nat` for nonnegative integer arithmetic and exposes `Int` bounds.
  Its input invariant is a sorted, disjoint list of closed grid intervals representing a
  symmetric set. Duplicate breakpoints contribute zero by the cell soundness proof.
- `Checker.checkWindow_sound` verifies admissible symmetric windows and transports the exact
  computed integer to the real probability bound. The native certificates are in `LeastPrime/Native`.

### Proposition 14 and theorem dependencies

The Proposition 14 certificate build took 6m19.958s wall time with the dependencies already
built. The native check for `tin_checked` in `LeastPrime/Native/Tin.lean` took 374 seconds and
verified `587142`. The native check for `tout_checked` in `LeastPrime/Native/Tout.lean` took
19 seconds and verified `595573`. Both integers equal the published values. The probability proofs
apply `Checker.checkWindow_sound` to pass from the exact integers to the real inequalities.

```text
'LeastPrime.p6_Tin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeastPrime.Native.tin_checked._native.native_decide.ax_1_1]
'LeastPrime.q5_Tout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeastPrime.Native.tout_checked._native.native_decide.ax_1_1]
'LeastPrime.main_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeastPrime.Native.tin_checked._native.native_decide.ax_1_1]
'LeastPrime.density_lower_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeastPrime.Native.tin_checked._native.native_decide.ax_1_1]
'LeastPrime.density_upper_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeastPrime.Native.tout_checked._native.native_decide.ax_1_1]
```

`main_four_of_cited` gives `C = 4`. The two `density_*_of_donnellyGrimmett` declarations make
the single analytic input used by Theorem 2 explicit.

The final local build, blueprint check and axiom audit passed. The audit checked 58 declarations
and type-checked all 18 native goals as exact Boolean checker equalities. The checker soundness
and recombination lemmas depend only on the standard axioms.

### Table 1

| Window | Paper lower | Lean lower | Paper upper | Lean upper | Comparison |
| --- | ---: | ---: | ---: | ---: | --- |
| `[0.14, 0.20]` | 0.596755 | 0.596755 | 0.604658 | 0.604658 | Equal |
| `[0.15, 0.19]` | 0.530857 | 0.530857 | 0.544968 | 0.544968 | Equal |
| `[0.15, 0.20]` | 0.561986 | 0.561986 | 0.572090 | 0.572090 | Equal |

The `[0.15, 0.20]` full lower evaluation took 624 seconds. The full `[0.15, 0.19]` evaluation
was stopped after 646 seconds to split the work. For each window the final proof divides the
interior gap and the terminal gap into three aligned ranges each. The step is 2223 grid units.
The interior cuts follow 90 and 180 steps, and the terminal cuts follow 22 and 44 steps.
`Checker.sumGridCells_split` proves additivity at aligned cuts. `Checker.probabilityBound_sixSlices`
proves equality with the original computation, including a single final rounding. The complete
unrounded sums are `530857971974` and `561986796550`, respectively.

`Checker.checkWindow_sound` transports each direct check to its real probability inequality.
`Checker.checkLowerSlice_sound` bounds the integral on each checked range, and
`Checker.checkLowerSixSlices_sound` certifies the probability using the exact recombination.
The local session ended before writing the final `[0.15, 0.19]` interior certificate. The cached
`lake build` retry completed that certificate and the library in 10m34.626s wall time. Lake
reported the following wall times for the individual successful checks.
The files are under `LeastPrime/Native`. Slice outputs are unrounded in square grid units.

| File | Lemma | Checked integer | Runtime |
| --- | --- | ---: | ---: |
| `DM1420Lower.lean` | `dm1420_lower_checked` | 596755 | 321s |
| `DM1420Upper.lean` | `dm1420_upper_checked` | 604658 | 23s |
| `DM1519Interior1.lean` | `dm1519_interior1_checked` | 118240780905 | 26s |
| `DM1519Interior2.lean` | `dm1519_interior2_checked` | 106923912498 | 171s |
| `DM1519Interior3.lean` | `dm1519_interior3_checked` | 115593539586 | 619s |
| `DM1519Tail1.lean` | `dm1519_tail1_checked` | 41721766398 | 227s |
| `DM1519Tail2.lean` | `dm1519_tail2_checked` | 36359207937 | 275s |
| `DM1519Tail3.lean` | `dm1519_tail3_checked` | 32018764650 | 238s |
| `DM1519Upper.lean` | `dm1519_upper_checked` | 544968 | 39s |
| `DM1520Interior1.lean` | `dm1520_interior1_checked` | 123389480097 | 20s |
| `DM1520Interior2.lean` | `dm1520_interior2_checked` | 113015399328 | 105s |
| `DM1520Interior3.lean` | `dm1520_interior3_checked` | 111569244120 | 330s |
| `DM1520Tail1.lean` | `dm1520_tail1_checked` | 42959261592 | 116s |
| `DM1520Tail2.lean` | `dm1520_tail2_checked` | 37758395259 | 119s |
| `DM1520Tail3.lean` | `dm1520_tail3_checked` | 33295016154 | 105s |
| `DM1520Upper.lean` | `dm1520_upper_checked` | 572090 | 26s |

### Reproduction

Run these commands from `least-prime-ap/lean` with the pinned toolchain.

```sh
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe cache get
lake build
lake env lean Blueprint.lean
python3 scripts/check_axioms.py
python3 scripts/regression.py /path/to/verify_split_divisor_density.cpp
```

## Open problems

The requested proof obligations are complete. Maynard and Donnelly–Grimmett remain the two
named analytic inputs to the conditional results.
