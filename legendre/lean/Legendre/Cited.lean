import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Legendre

open Complex Set
open scoped BigOperators

/-- Zeros of the Riemann zeta function in the open critical strip. -/
def nontrivialZeros : Set ℂ := {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}

private noncomputable def regularizedCompletedZeta (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

private theorem differentiable_regularizedCompletedZeta :
    Differentiable ℂ regularizedCompletedZeta :=
  ((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))

private theorem regularizedCompletedZeta_eq_zero {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    regularizedCompletedZeta ρ = 0 := by
  rcases hρ with ⟨hre, hre', hz⟩
  have h₀ : ρ ≠ 0 := by
    intro h
    simp [h] at hre
  have h₁ : ρ ≠ 1 := by
    intro h
    simp [h] at hre'
  have hc : completedRiemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero h₀, div_eq_zero_iff] at hz
    exact hz.resolve_right (Gammaℝ_ne_zero_of_re_pos hre)
  have hsub : 1 - ρ ≠ 0 := sub_ne_zero.mpr h₁.symm
  calc
    regularizedCompletedZeta ρ = ρ * (ρ - 1) * completedRiemannZeta ρ := by
      rw [regularizedCompletedZeta, completedRiemannZeta_eq]
      field_simp [h₀, hsub]
      ring
    _ = 0 := by rw [hc, mul_zero]

/-- There are finitely many nontrivial zeros in each bounded closed box. -/
theorem finite_nontrivialZeros_in_box (a b c d : ℝ) :
    (nontrivialZeros ∩ (Icc a b ×ℂ Icc c d)).Finite := by
  have ha : AnalyticOnNhd ℂ regularizedCompletedZeta univ :=
    fun z _ ↦ differentiable_regularizedCompletedZeta.analyticAt z
  have hn : regularizedCompletedZeta 0 ≠ 0 := by simp [regularizedCompletedZeta]
  have hz := mem_codiscrete'.1 (ha.preimage_zero_mem_codiscrete hn)
  have hbox : IsCompact (Icc a b ×ℂ Icc c d) := isCompact_Icc.reProdIm isCompact_Icc
  have hclosed : IsClosed (regularizedCompletedZeta ⁻¹' ({0} : Set ℂ)) :=
    isClosed_singleton.preimage differentiable_regularizedCompletedZeta.continuous
  have hd : IsDiscrete (regularizedCompletedZeta ⁻¹' ({0} : Set ℂ)) := by
    simpa only [preimage_compl, compl_compl] using hz.2
  have hf := (hbox.inter_right hclosed).finite (hd.mono inter_subset_right)
  exact hf.subset fun ρ ⟨hρ, hboxρ⟩ ↦ ⟨hboxρ, regularizedCompletedZeta_eq_zero hρ⟩

private theorem finite_zerosIn (l u : ℝ) :
    (nontrivialZeros ∩ im ⁻¹' Icc l u).Finite :=
  (finite_nontrivialZeros_in_box 0 1 l u).subset fun _ ⟨hρ, him⟩ ↦
    ⟨hρ, mem_reProdIm.mpr ⟨⟨hρ.1.le, hρ.2.1.le⟩, him⟩⟩

/-- Critical-strip zeros with imaginary part in `[l,u]`, listed once each. -/
noncomputable def zerosIn (l u : ℝ) : Finset ℂ := (finite_zerosIn l u).toFinset

@[simp] theorem mem_zerosIn {l u : ℝ} {ρ : ℂ} :
    ρ ∈ zerosIn l u ↔ ρ ∈ nontrivialZeros ∧ l ≤ ρ.im ∧ ρ.im ≤ u := by
  simp [zerosIn]

/-- The analytic order of vanishing at a nontrivial zero. -/
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

theorem zeroMultiplicity_eq_order {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    (zeroMultiplicity ρ : ℕ∞) = analyticOrderAt riemannZeta ρ := by
  have ha : AnalyticOnNhd ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
    (show DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ from
      fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt).analyticOnNhd
        isOpen_compl_singleton
  have hc : IsConnected ({1} : Set ℂ)ᶜ := by
    apply isConnected_compl_singleton_of_one_lt_rank
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have h₀ : (0 : ℂ) ∈ ({1} : Set ℂ)ᶜ := by simp
  have h₁ : ρ ∈ ({1} : Set ℂ)ᶜ := by
    intro h
    have hre := hρ.2.1
    simp [show ρ = 1 from h] at hre
  have hz : analyticOrderAt riemannZeta 0 = 0 :=
    (ha 0 h₀).analyticOrderAt_eq_zero.mpr (by rw [riemannZeta_zero]; norm_num)
  have hfin := ha.analyticOrderAt_ne_top_of_isPreconnected hc.isPreconnected h₀ h₁ (by simp [hz])
  exact ENat.coe_toNat hfin

/-- The number of nontrivial zeros with `0 < Im ρ ≤ t`, counting multiplicity. -/
noncomputable def zeroCount (t : ℝ) : ℕ := by
  classical
  exact ∑ ρ ∈ (zerosIn 0 t).filter (fun ρ ↦ 0 < ρ.im), zeroMultiplicity ρ

/-- Chebyshev's ψ with half weight at an integral endpoint. -/
noncomputable def psiZero (x : ℝ) : ℝ := by
  classical
  exact Chebyshev.psi x - if (⌊x⌋₊ : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0

/-- Distance from `x` to the closest prime power other than `x` itself. -/
noncomputable def primePowerDistance (x : ℝ) : ℝ :=
  Metric.infDist x {y : ℝ | ∃ n : ℕ, IsPrimePow n ∧ y = n ∧ y ≠ x}

/-- Davenport's remainder after removing the pole, zero and trivial-zero terms. -/
noncomputable def explicitFormulaError (x T : ℝ) : ℂ := by
  classical
  let zeroSum := ∑ ρ ∈ (zerosIn (-T) T).filter (fun ρ ↦ |ρ.im| < T),
    (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)
  exact (psiZero x : ℂ) - ((x : ℂ) - zeroSum - (Real.log (2 * Real.pi) : ℂ) -
    (Real.log (1 - x⁻¹ ^ 2) / 2 : ℝ))

/-- The number of primes in `(x,x+t]` for `x ≥ 0` and `t ≥ 0`. -/
noncomputable def primeCountIn (x t : ℝ) : ℕ :=
  Nat.primeCounting ⌊x + t⌋₊ - Nat.primeCounting ⌊x⌋₊

/-- The published inputs to the proof. -/
structure CitedFacts : Prop where
  /-- Sorenson and Webster, *An algorithm and computation to verify Legendre's conjecture*,
  §5, Research in Number Theory 11, article 4 (2025). -/
  sorensonWebster : ∀ m : ℕ, 2 ≤ m → m ≤ 70_500_000_000_000 →
    (∃ p : ℕ, p.Prime ∧ m ^ 2 < p ∧ p < m * (m + 1)) ∧
    (∃ p : ℕ, p.Prime ∧ m * (m + 1) < p ∧ p < (m + 1) ^ 2)

  /-- Carneiro, Milinovich and Soundararajan, *Fourier optimization and prime gaps*,
  Theorem 1.5 (Theorem 5 in the preprint). -/
  cms : RiemannHypothesis → ∀ u : ℝ, 4 ≤ u →
    ∃ p : ℕ, p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ u + (22 / 25) * Real.sqrt u * Real.log u

  /-- Davenport, *Multiplicative Number Theory*, Chapter 17, equations (9)–(10). -/
  explicitFormula : ∃ C : ℝ, 0 ≤ C ∧ ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖explicitFormulaError x T‖ ≤ C * (x * Real.log (x * T) ^ 2 / T +
      Real.log x * min 1 (x / (T * primePowerDistance x)))

  /-- Trudgian, *An improved upper bound for the argument of the Riemann zeta-function on the
  critical line II*, Corollary 1, with its lower height parameter specialised to `t`. -/
  trudgian : ∀ t : ℝ, Real.exp 1 ≤ t →
    |(zeroCount t : ℝ) - t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) - 7 / 8| ≤
      0.112 * Real.log t + 0.278 * Real.log (Real.log t) + 2.510 + 0.2 / t

  /-- Montgomery and Vaughan, *The large sieve*, Theorem 2, equation (1.12). -/
  montgomeryVaughan : ∀ x t : ℝ, 0 < x → 1 < t →
    (primeCountIn x t : ℝ) ≤ 2 * t / Real.log t

end Legendre
