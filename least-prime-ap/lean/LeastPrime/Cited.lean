import LeastPrime.Statement
import Mathlib.Data.Nat.Factors
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The two external inputs and the probability measures used to state them. -/

namespace LeastPrime

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Mix finitely many probability measures with probabilities proportional to positive weights. -/
def weightedMixture {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (weight : ι → ℝ) (hpos : ∀ i, 0 < weight i)
    (law : ι → ProbabilityMeasure Ω) : ProbabilityMeasure Ω := by
  let total := ∑ i, weight i
  have htotal : 0 < total := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  let prob (i : ι) := ENNReal.ofReal (weight i / total)
  have hprob : ∑ i, prob i = 1 := by
    have hnonneg (i : ι) (_ : i ∈ Finset.univ) : 0 ≤ weight i / total :=
      div_nonneg (hpos i).le htotal.le
    change ∑ i, ENNReal.ofReal (weight i / total) = 1
    rw [← ENNReal.ofReal_sum_of_nonneg hnonneg, ← Finset.sum_div,
      show ∑ i, weight i = total from rfl, div_self htotal.ne', ENNReal.ofReal_one]
  refine ⟨∑ i, prob i • (law i : Measure Ω), ⟨?_⟩⟩
  simpa [Measure.finset_sum_apply] using hprob

private theorem measurable_cons {j : ℕ} (a : ℝ) :
    Measurable (Fin.cons (α := fun _ : Fin (j + 1) => ℝ) a) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simpa using (measurable_pi_apply i : Measurable (fun v : Fin j → ℝ => v i))

/-- The size-biased law for a list of positive logarithms. Each step chooses an index with
probability proportional to its logarithm, records the share of the original `logN`, and removes
that occurrence. Once the list is exhausted the remaining coordinates are zero. -/
def sizeBiasedFromLogs (logN : ℝ) : (j : ℕ) → List {w : ℝ // 0 < w} →
    ProbabilityMeasure (Fin j → ℝ)
  | 0, _ => ⟨Measure.dirac 0, inferInstance⟩
  | j + 1, [] => ⟨Measure.dirac 0, inferInstance⟩
  | j + 1, first :: rest =>
    let weights := first :: rest
    weightedMixture (ι := Fin (rest.length + 1)) (fun i => (weights[i.val] : ℝ))
      (fun i => weights[i.val].property) (fun i =>
        (sizeBiasedFromLogs logN j (weights.eraseIdx i.val)).map
          (measurable_cons ((weights[i.val] : ℝ) / logN)).aemeasurable)

/-- The prime-factor logarithms of `n` in decreasing order, with one entry per occurrence. -/
def primeLogs (n : ℕ) : List {w : ℝ // 0 < w} :=
  n.primeFactorsList.reverse.attach.map fun p =>
    ⟨Real.log (p.val : ℝ), Real.log_pos (by
      have hp : p.val ∈ n.primeFactorsList := List.mem_reverse.mp p.property
      exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).one_lt)⟩

/-- The conditional law of the first `j` size-biased log-shares given `n`. -/
def sizeBiasedLaw (j n : ℕ) : ProbabilityMeasure (Fin j → ℝ) :=
  sizeBiasedFromLogs (Real.log n) j (primeLogs n)

theorem sizeBiasedLaw_one (j : ℕ) :
    (sizeBiasedLaw j 1 : Measure (Fin j → ℝ)) = Measure.dirac 0 := by
  have hlogs : primeLogs 1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [primeLogs]
  rw [sizeBiasedLaw, hlogs]
  cases j <;> rfl

/-- The law obtained by taking `n` uniform on `1, …, X` and sampling its size-biased order.
At `X = 0` it is extended by the point mass at zero. -/
def averageLaw (j : ℕ) : ℕ → ProbabilityMeasure (Fin j → ℝ)
  | 0 => ⟨Measure.dirac 0, inferInstance⟩
  | X + 1 => weightedMixture (ι := Fin (X + 1)) (fun _ => 1) (fun _ => zero_lt_one)
      (fun i => sizeBiasedLaw j (i.val + 1))

/-- The probability-measure form of the finite GEM(1) marginal. -/
def stickProbability (j : ℕ) : ProbabilityMeasure (Fin j → ℝ) :=
  ⟨stickLaw j, inferInstance⟩

/-- The analytic inputs used by the paper. -/
structure CitedFacts : Prop where
  /-- Maynard, *Primes in arithmetic progressions to large moduli III*, Corollary 1.4,
  Memoirs AMS 1544 (2025), compared with arXiv:2006.08250v1. The published divisor exponent
  is `2/5 + 5η`. Fix `A = 1`, specialize to positive natural moduli, and enlarge `x₀` to at least
  two. The positive lower comparison with `π(x) / φ(q)` then gives a prime in each reduced class. -/
  maynard : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ < x → ∃ bad : Finset ℕ,
      (∀ q ∈ bad, 1 ≤ q ∧ (q : ℝ) ≤ x ^ (1 / 2 + η)) ∧
      (bad.card : ℝ) ≤ x ^ (1 / 2 + η) / Real.log x ∧
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ x ^ (1 / 2 + η) → q ∉ bad →
        (∃ d ∈ q.divisors, x ^ (2 / 5 + 5 * η) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x ^ (3 / 7 : ℝ)) →
        AllClassesBelow q x
  /-- Donnelly–Grimmett, *On the asymptotic distribution of large prime factors*,
  J. London Math. Soc. (2) 47 (1993), Corollary 2, using the published version.
  Equation (2.1) gives the same law after summing over occurrences of each prime.
  Corollary 2 uses `log N` and zero padding. Coordinate projection gives the finite-dimensional
  marginal of the GEM(1) limit. -/
  donnellyGrimmett : ∀ j : ℕ, 0 < j → Tendsto (averageLaw j) atTop (𝓝 (stickProbability j))

end

end LeastPrime
