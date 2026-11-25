import Chowla.Zeros
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace Chowla

open Filter
open scoped BigOperators Topology

noncomputable def nonvanishingIndicator (d : ℤ) : ℝ := by
  classical
  exact if CentralNonvanishing d then 1 else 0

private theorem quadraticL_analyticAt_half {d : ℤ} (hd : 1 < |d|) :
    AnalyticAt ℂ (quadraticL d) (1 / 2) := by
  have hN : 1 < d.natAbs := by
    rw [Int.abs_eq_natAbs] at hd
    exact_mod_cast hd
  letI : NeZero d.natAbs := ⟨by omega⟩
  have heq : quadraticL d = DirichletCharacter.LFunction (chi d) :=
    funext (quadraticL_eq d)
  rw [heq]
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction (chi d)) ({1}ᶜ : Set ℂ) := by
    intro s hs
    exact (DirichletCharacter.differentiableAt_LFunction (chi d) s
      (.inl (by simpa using hs))).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_compl_singleton _ (by norm_num)

private theorem two_le_central_order (c : CitedFacts) {d : ℤ}
    (hd : IsFundDisc d) (hd' : 1 < |d|) (hz : quadraticL d (1 / 2) = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (quadraticL d) (1 / 2) := by
  obtain ⟨k, hk⟩ := even_central_order c d hd hd'
  have hne := (quadraticL_analyticAt_half hd').analyticOrderAt_ne_zero.mpr hz
  have hkpos : 0 < k := by
    by_contra! h
    have heq : k = 0 := by omega
    rw [hk, heq, mul_zero] at hne
    exact hne rfl
  rw [hk]
  change ((2 : ℕ) : ℕ∞) ≤ ((2 * k : ℕ) : ℕ∞)
  exact ENat.coe_le_coe.mpr (by omega)

/-- A central zero contributes at least two copies of the squared value at zero. -/
theorem pointwise_vanishing_bound (c : CitedFacts) (d : ℤ) (X : ℝ) (A : ℝ → ℝ)
    (hd : IsFundDisc d) (hd' : 1 < |d|) (hA : A 0 = 1)
    (hs : Summable (fun z : ZeroCopy d => (zeroSummand A d X z)^2)) :
    2 * (1 - nonvanishingIndicator d) ≤ ∑' z : ZeroCopy d, (zeroSummand A d X z)^2 := by
  classical
  by_cases h : CentralNonvanishing d
  · have hn : 0 ≤ ∑' z : ZeroCopy d, (zeroSummand A d X z)^2 :=
      tsum_nonneg (fun _ => sq_nonneg _)
    simpa [nonvanishingIndicator, h] using hn
  · have hz : quadraticL d (1 / 2) = 0 := by simpa [CentralNonvanishing] using h
    have ht := two_le_central_order c hd hd' hz
    let s : {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ quadraticL d s = 0} :=
      ⟨1 / 2, by norm_num [Complex.div_re], by norm_num [Complex.div_re], hz⟩
    let z₀ : ZeroCopy d := ⟨s, ⟨0, lt_of_lt_of_le (by norm_num) ht⟩⟩
    let z₁ : ZeroCopy d := ⟨s, ⟨1, lt_of_lt_of_le (by norm_num) ht⟩⟩
    have hne : z₀ ≠ z₁ := by
      intro he
      have hj := congrArg (fun z : ZeroCopy d => z.2.val) he
      exact Nat.zero_ne_one hj
    have hz₀ : zeroSummand A d X z₀ = 1 := by
      simpa [zeroSummand, ZeroCopy.ordinate, z₀, s, Complex.div_im] using hA
    have hz₁ : zeroSummand A d X z₁ = 1 := by
      simpa [zeroSummand, ZeroCopy.ordinate, z₁, s, Complex.div_im] using hA
    have hb := hs.sum_le_tsum {z₀, z₁} (fun _ _ => sq_nonneg _)
    norm_num [nonvanishingIndicator, h, Finset.sum_pair hne, hz₀, hz₁] at hb ⊢
    exact hb

end Chowla
