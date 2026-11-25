# Lean formalisation of the 11/5-powers theorem

## Main results

The three statement files were approved in draft PR #66 and match the approved commit `a52fbee`. The project formalises Theorems 1, 2 and 4 from the stated premises. The source for the theorem numbers is the 24 November 2026 paper at commit `cb8d8ff17702270e77d649c45ea473d45e19524d` in `maths-releases`. [Paper source](https://github.com/charlieoneill11/maths-releases/blob/cb8d8ff17702270e77d649c45ea473d45e19524d/legendre/paper/main.tex)

The proved public theorem types are listed below.

```lean
Legendre.outer_of (hRH : RiemannHypothesis) (h : Legendre.CitedFacts) : Legendre.OuterStatement
Legendre.squares_of (h : Legendre.CitedFacts) (c : Legendre.ComputationClaims) : Legendre.SquaresStatement
Legendre.main_of (hRH : RiemannHypothesis) (h : Legendre.CitedFacts)
  (c : Legendre.ComputationClaims) : Legendre.MainStatement
```

## Toolchain and RH

The project uses Lean `v4.29.1` and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`, the seven-cycle pins. The project takes Mathlib's `RiemannHypothesis` as a premise. The RH mirror's `original` commit `40e56bab026552e089d7afcfeff08d2defb9c005` confirms Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The preservation mirror documents roughly 105 GB of free disk for the published cache, compared with roughly 59 GB available in the workspace when checked. It documents a source build requiring hours and potentially around 1 TB of temporary files. The current community branch uses Lean `v4.37.0-rc1` and a different Mathlib revision. The local axiom audit covers this project's declarations. The upstream `riemannHypothesis` was not imported or audited locally. [Original toolchain](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/lean-toolchain) · [Original manifest](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/lake-manifest.json) · [Cache requirements](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/774b9e8022f50d20be861ecc9d609cfc26436a81/verification/CACHE.md)

## Published inputs

| `CitedFacts` field | Source and transcription |
| --- | --- |
| `sorensonWebster` | Sorenson and Webster, Research in Number Theory **11**, article 4 (2025), §§4–5. The paper reports the two half-intervals through 70,500,000,000,000. At every base used by the field, each of the three integer endpoints is composite. [Version of record](https://doi.org/10.1007/s40993-024-00589-4) |
| `cms` | Carneiro, Milinovich and Soundararajan, Comment. Math. Helv. **94** (2019), 533–568, Theorem **1.5** in the journal and Theorem **5** in the preprint. The interval starts at the real input and includes both endpoints. [Journal](https://doi.org/10.4171/CMH/467) · [Published text](https://www.e-periodica.ch/cntmng?pid=com-001%3A2019%3A94%3A%3A697) · [Author preprint](https://arxiv.org/pdf/1708.04122) |
| `explicitFormula` | Davenport, Chapter 17, equations (9)–(10), including the strictly truncated zero sum and the distance to another prime power. The equation and bound were checked against the accessible second edition. The pages of the requested third edition still need direct comparison. [Chapter](https://doi.org/10.1007/978-1-4757-5927-3_17) · [Second edition text](https://djvu.online/file/Rh8B8jEVpxFgk) |
| `trudgian` | Trudgian, J. Number Theory **134** (2014), 280–292, Corollary 1. The journal abstract confirms the published constants. The preprint states the corollary with different constants and the `0.2/T₀` term. Taking its lower height parameter `T₀ = T` gives the displayed form with `0.2/T`. A later zero-counting paper also transcribes the journal corollary in this form. Direct comparison with the journal pages remains open. [Journal record](https://doi.org/10.1016/j.jnt.2013.07.017) · [Author preprint](https://arxiv.org/pdf/1208.5846) · [Cross-check, Table 3](https://hexagonmath.org/pdf/2611.00157v2) |
| `montgomeryVaughan` | Montgomery and Vaughan, Mathematika **20** (1973), 119–134, Theorem 2 and (1.12). The source uses positive real starting points and the count in `(x,x+t]`. The field uses the non-strict bound in (1.12). [Author copy](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf) |

```lean
sorensonWebster : ∀ m : ℕ, 2 ≤ m → m ≤ 70_500_000_000_000 →
  (∃ p : ℕ, p.Prime ∧ m ^ 2 < p ∧ p < m * (m + 1)) ∧
  (∃ p : ℕ, p.Prime ∧ m * (m + 1) < p ∧ p < (m + 1) ^ 2)

cms : RiemannHypothesis → ∀ u : ℝ, 4 ≤ u →
  ∃ p : ℕ, p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ u + (22 / 25) * Real.sqrt u * Real.log u

explicitFormula : ∃ C : ℝ, 0 ≤ C ∧ ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
  ‖explicitFormulaError x T‖ ≤ C * (x * Real.log (x * T) ^ 2 / T +
    Real.log x * min 1 (x / (T * primePowerDistance x)))

trudgian : ∀ t : ℝ, Real.exp 1 ≤ t →
  |(zeroCount t : ℝ) - t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) - 7 / 8| ≤
    0.112 * Real.log t + 0.278 * Real.log (Real.log t) + 2.510 + 0.2 / t

montgomeryVaughan : ∀ x t : ℝ, 0 < x → 1 < t →
  (primeCountIn x t : ℝ) ≤ 2 * t / Real.log t
```

Mathlib supplies Chebyshev's `psi`, the von Mangoldt function, `Nat.primeCounting`, zeta analyticity, and analytic order. `zeroCount` is an integer sum of analytic multiplicities, and `finite_nontrivialZeros_in_box` derives finiteness from the isolated zeros of the pole-removed completed zeta function. The search in Mathlib, the RH mirror and PrimeNumberTheoremAnd found no proved Lean version of the five fields suitable for this toolchain. PrimeNumberTheoremAnd at `e9906138410f8f76ca66b9bc252d0993f3ee348c` has CMS and Trudgian stubs in `IEANTN/TMEEMT.lean` and a smoothed explicit formula at a different test-function interface. [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/e9906138410f8f76ca66b9bc252d0993f3ee348c/PrimeNumberTheoremAnd/IEANTN)

## Computation premises

Both fields are sourced from the completed combined verification in `COVERAGE.md` and §§5.3–5.4 of the paper. The squares premise starts immediately after the published prefix. The powers premise starts immediately after the square nesting range and stops before the analytic cutoff. [Coverage ledger](https://github.com/charlieoneill11/maths-releases/blob/cb8d8ff17702270e77d649c45ea473d45e19524d/legendre/computation/COVERAGE.md)

```lean
squares : ∀ m : ℕ, 70_500_000_000_000 < m → m ≤ 10 ^ 14 →
  ∃ p : ℕ, p.Prime ∧ m ^ 2 < p ∧ p < (m + 1) ^ 2
powers : ∀ n : ℕ, 5_336_699_231_206 < n → n < 35 * 10 ^ 12 →
  ∃ p : ℕ, p.Prime ∧ n ^ 11 < p ^ 5 ∧ p ^ 5 < (n + 1) ^ 11
```

## Proof status

| Paper item | Lean declaration | Status |
| --- | --- | --- |
| Lemma 7 | `powerEndpoint_ne_prime`, `powerInterval_iff` | Proved |
| Lemma 8 | `prime_in_shifted_square` | Proved |
| Proposition 3 | `low_range`, `low_range_cutoff` | Proved |
| Lemma 9 | `square_interval_nested` | Proved |
| Lemma 10, Corollary 11 | `prime_in_cms_interval`, `far_range` | Proved |
| Definition 12, Lemma 13 | `CosineTest`, `cosine_fourier_spec` | Defined and proved |
| Lemma 14 | `smoothed_explicit_formula` | Proved on the support used in Proposition 22 |
| Lemma 15 | `zeroCount_error` | Proved |
| Lemma 16 | `zero_sum_bound` | Proved |
| Proposition 17 | `gap_condition` | Proved for the empty correction set used in Proposition 22 |
| Lemma 18 | `shoulder_lengths` | Proved |
| Lemmas 19–20 | `twelve_mode_bounds`, `twelve_mode_cell_bounds` | Proved |
| Lemma 21 | `shoulder_sum_bound` | Proved |
| Proposition 22 | `bridge_row_checks`, `bridge_error_bounds`, `bridge_range` | Proved |
| Theorem 4 | `outer_of` | Proved from RH and `CitedFacts` |
| Lemma 23 and public replay | — | Optional milestone |
| Theorem 2, Proposition 5, Theorem 1 | `squares_of`, `finite_range`, `main_of` | Proved from the stated premises |

### Changes to the proof route

- Proposition 3 may use the square base \(n^{11/10}\) itself. Lemma 7 excludes equality with a prime at the lower power endpoint, giving the required strict bound.
- Lemma 14 integrates Davenport's estimate against the compactly supported derivative and uses dominated convergence. The local version takes the support above 2, which the window in Proposition 22 satisfies. The paper's more general support condition puts the lower endpoint above 1, while the truncated input used in its proof applies from 2.
- For Lemma 15 below \(e\), monotonicity and the cited estimate at \(e\) give \(N(t)\le N(e)\le2\). For Lemma 16, integration starts at height zero and the boundary term \((7/8)|F(0)|\) fits in the paper's existing error allowance. An elementary bound on Mathlib's theta-integral representation proves \(\zeta(1/2)\ne0\).
- The asymptotic cosine and derivative bounds follow from integration by parts. For the two variation integrals in Lemma 19, the estimates of 19 on \([0,16]\) and \(64/y^2\) above 16 suffice for the same bounds 625 and 2000.
- Lemma 21 uses the source's half-open interval and adds a one-prime allowance for the closed-interval count. Proposition 22 proves monotonicity from the checked slope coefficient using \(e^t\ge1+t\) and the corresponding logarithmic increment bound.
- The executable logarithm uses a range-reduced 24-term artanh series and Mathlib's remainder bound, with directed rounding to multiples of \(2^{-200}\). Cosine uses verified alternating Taylor brackets, Mathlib's 20-decimal bounds for \(\pi\), and directed rounding at \(10^{-18}\). Tenth roots use integer bisection at \(2^{-200}\). Table 1 charge terms round upwards at \(10^{-20}\).

## Build and axiom checks

```sh
lake exe cache get
lake build
lake env lean Blueprint.lean
python3 scripts/check_axioms.py
```

The final workspace `lake build` took 4 min 9.876 s with the pinned Mathlib cache. This run rebuilt the Fourier checkers and the final theorem modules. The workflow runs the build, blueprint and audit on both branch pushes and pull requests. The audit passed for 60 declarations and five native checks. It checks the compiled type of each direct native equality and audits its soundness theorem separately.

```text
'Legendre.outer_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Legendre.grid_mass_verified._native.native_decide.ax_1_1,
 Legendre.grid_moment_verified._native.native_decide.ax_1_1,
 Legendre.shoulderHead_check._native.native_decide.ax_1_1,
 Legendre.Arithmetic.firstRow_charge_verified._native.native_decide.ax_1_1,
 Legendre.Arithmetic.secondRow_charge_verified._native.native_decide.ax_1_1]
'Legendre.squares_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Legendre.main_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Legendre.grid_mass_verified._native.native_decide.ax_1_1,
 Legendre.grid_moment_verified._native.native_decide.ax_1_1,
 Legendre.shoulderHead_check._native.native_decide.ax_1_1,
 Legendre.Arithmetic.firstRow_charge_verified._native.native_decide.ax_1_1,
 Legendre.Arithmetic.secondRow_charge_verified._native.native_decide.ax_1_1]
```

### Native checks

Each time is wall time for the individual Boolean proof with its imports already built. These measurements ran with up to two independent checks active. The three short Table 1 base and error checks and the check at `F₁₂(0)` use `decide +kernel`.

| Native declaration | File under `Legendre/Native/` | Real conclusion from the soundness theorem | Wall time |
| --- | --- | --- | ---: |
| `shoulderHead_check` | `ShoulderGrid.lean` | `shoulderHeight_steps_of_check` proves the monotone height majorant of Lemma 20, including `e₁ < 0.76`. | 42.720 s |
| `firstRow_charge_verified` | `BridgeNumeric.lean` | `rowChargeChecker_sound` bounds the logarithmic offsets and the first real shoulder charge. | 30.796 s |
| `secondRow_charge_verified` | `BridgeNumeric.lean` | `rowChargeChecker_sound` bounds the logarithmic offsets and the second real shoulder charge. | 30.720 s |
| `grid_mass_verified` | `FourierGrid.lean` | `checkGridMass_integral_sound` bounds twice the integral of `|F₁₂|` on `[0,16]` by `0.7658655`. | 86.442 s |
| `grid_moment_verified` | `FourierGrid.lean` | `checkGridMoment_integral_sound` bounds twice the integral of `|F₁₂(y)| log y` on `[0,16]` by `−1.379585`. | 134.570 s |

## Numerical regression

The standard-library Python oracle ran in 22.3 seconds. The comparisons below are diagnostic. The Lean proofs establish the real claims through the verified enclosures and integration bounds.

| Check | Python baseline | Lean comparison |
| --- | --- | --- |
| `F₁₂(0)` lower bound | 1.000000634064472 | Same displayed digits. The kernel checks `1.00000063` as a strict lower bound. |
| Doubled mass on `[0,16]` | 0.7658650396040396 | Same displayed digits. The exact difference in the evaluated upper sums is `+10⁻²¹`. |
| Doubled log moment on `[0,16]` | −1.379588053299503 | Same displayed digits. The evaluated upper sum increases by about `1.17903 × 10⁻²⁰`. |
| Doubled mass tail | `3.985288585548387 × 10⁻⁶` | `3.986354166666667 × 10⁻⁶` after rounding the tail coefficients outwards. |
| Doubled log-moment tail | `1.238794289962176 × 10⁻⁵` | `1.239294482638889 × 10⁻⁵` with the rounded coefficients and `log 16 < 2.773`. |
| Shoulder charges | 0.098158791049, 0.098418988075 | Same displayed digits. Lean rounded upwards to 0.09815879104910680305 and 0.0984189880747696213. |
| `Jₖ(l)` lower bounds | 0.003010957636, 0.076965172408 | Same displayed digits. Lean's comparison bounds are about 0.003010957635862793 and 0.07696517240761765. |
| Slope lower bounds | 1.477645031214, 1.489296380881 | Same displayed digits. Lean's bounds are about 1.477645031213824 and 1.489296380881393. |
| Uniform error upper bound | `1.055185073 × 10⁻⁹` | `1.076129158 × 10⁻⁹` using `P < 34` and including the `10⁻¹²` allowance from Proposition 17. The kernel checks that the total is below `1.1 × 10⁻⁹`. |
| CMS comparison margin | About 0.103372 | The independent Lean calculation proves a lower bound of `0.1` from a tenth-root lower bound of `30.0479` and logarithm upper bound of `34.028`. |

All 64,001 Fourier nodes were compared, including all 12 removable singularities. Exactly five intervals differ. The lower endpoint moves down by `10⁻¹⁸` at grid indices 300, 350 and 371. The upper endpoint moves up by `10⁻¹⁸` at indices 1088 and 2071. All other Fourier pairs agree exactly. The two sets of logarithm enclosures overlap at all 64,000 positive nodes. In 1,671 cases the Decimal centre lies outside the narrower Lean enclosure by at most `4.992 × 10⁻⁴⁹`, while the widened Python interval still intersects it.

The 20-decimal \(\pi\) bounds increase the shoulder suffix majorants at exactly the paper indices 141, 332, 424, 581, 675, 720, 774, 895, 900, 955 and 2901. The largest increase is `2.32962 × 10⁻¹⁹`. The first height and both Table 1 shoulder charges agree with the oracle to the displayed precision.

## Open items

Direct comparison with the third edition pages of Davenport and the journal pages of Trudgian remains open. The third-edition catalogue points to library copies, and the publisher's Trudgian PDF returned HTTP 403. The optional public certificate replay was outside this implementation. [Davenport third-edition record](https://openlibrary.org/books/OL6791980M/Multiplicative_number_theory) · [Trudgian journal PDF](https://www.sciencedirect.com/science/article/pii/S0022314X13002047/pdf)
