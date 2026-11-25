import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Hermite–Hadamard bounds for the reciprocal affine functions used in level two. -/

namespace LeastPrime

open MeasureTheory Set

private theorem integral_affine_Icc (a b c d : ℝ) (hab : a ≤ b) :
    (∫ r in Icc a b, c + d * r) = (b - a) * (c + d * ((a + b) / 2)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h : Continuous (fun r : ℝ => d * r) := continuous_const.mul continuous_id
  rw [intervalIntegral.integral_add intervalIntegrable_const (h.intervalIntegrable a b)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

private theorem integral_inv_bounds {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    let m := (a + b) / 2
    (b - a) / m ≤ (∫ r in Icc a b, 1 / r) ∧
      (∫ r in Icc a b, 1 / r) ≤ (b - a) * ((1 / a + 1 / b) / 2) := by
  let m := (a + b) / 2
  have hb : 0 < b := ha.trans hab
  have hm : 0 < m := by dsimp [m]; positivity
  let tangent (r : ℝ) := 2 / m - r / m ^ 2
  let secant (r : ℝ) := (a + b - r) / (a * b)
  have ht : ∀ r ∈ Icc a b, tangent r ≤ 1 / r := by
    intro r hr
    have hpos : 0 < r := ha.trans_le hr.1
    dsimp [tangent]
    have heq : 1 / r - (2 / m - r / m ^ 2) = (r - m) ^ 2 / (r * m ^ 2) := by
      field_simp [hpos.ne', hm.ne']; ring
    have hnonneg : 0 ≤ (r - m) ^ 2 / (r * m ^ 2) := by positivity
    linarith
  have hs : ∀ r ∈ Icc a b, 1 / r ≤ secant r := by
    intro r hr
    have hpos : 0 < r := ha.trans_le hr.1
    dsimp [secant]
    have heq : (a + b - r) / (a * b) - 1 / r = (r - a) * (b - r) / (a * b * r) := by
      field_simp [hpos.ne', ha.ne', hb.ne']; ring
    have hnonneg : 0 ≤ (r - a) * (b - r) / (a * b * r) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)) (by positivity)
    linarith
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Icc a b) := by
    refine (continuousOn_const.div continuousOn_id ?_).integrableOn_compact isCompact_Icc
    intro r hr
    exact (ha.trans_le hr.1).ne'
  have htan : IntegrableOn tangent (Icc a b) := by
    exact (continuous_const.sub (continuous_id.div_const _)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hsec : IntegrableOn secant (Icc a b) := by
    exact ((continuous_const.sub continuous_id).div_const _).continuousOn.integrableOn_compact
      isCompact_Icc
  have h1 := setIntegral_mono_on htan hint measurableSet_Icc ht
  have h2 := setIntegral_mono_on hint hsec measurableSet_Icc hs
  have htan_eq : tangent = fun r => 2 / m + (-(1 / m ^ 2)) * r := by
    funext r
    dsimp [tangent]
    ring
  have hsec_eq : secant = fun r => (a + b) / (a * b) + (-(1 / (a * b))) * r := by
    funext r
    dsimp [secant]
    ring
  rw [htan_eq, integral_affine_Icc a b _ _ hab.le] at h1
  rw [hsec_eq, integral_affine_Icc a b _ _ hab.le] at h2
  have htan_val : 2 / m + (-(1 / m ^ 2)) * ((a + b) / 2) = 1 / m := by
    change 2 / m + (-(1 / m ^ 2)) * m = 1 / m
    field_simp [hm.ne']; ring
  have hsec_val : (a + b) / (a * b) + (-(1 / (a * b))) * ((a + b) / 2) =
      (1 / a + 1 / b) / 2 := by
    field_simp [ha.ne', hb.ne']; ring
  rw [htan_val, ← div_eq_mul_one_div] at h1
  rw [hsec_val] at h2
  exact ⟨h1, h2⟩

private theorem integral_reciprocal_affine {a b α β : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Icc a b, α + β / r) =
      (b - a) * α + β * ∫ r in Icc a b, 1 / r := by
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    div_eq_mul_one_div β]
  have hint : IntervalIntegrable (fun r : ℝ => 1 / r) volume a b := by
    refine ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_const.div continuousOn_id ?_)
    intro r hr
    exact (ha.trans_le hr.1).ne'
  rw [intervalIntegral.integral_add intervalIntegrable_const (hint.const_mul β),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]

/-- Lemma 13 for a nonnegative reciprocal coefficient. -/
theorem hermite_hadamard_inv {a b α β : ℝ} (ha : 0 < a) (hab : a < b) (hβ : 0 ≤ β) :
    let f (r : ℝ) := α + β / r
    (b - a) * f ((a + b) / 2) ≤ (∫ r in Icc a b, f r) ∧
      (∫ r in Icc a b, f r) ≤ (b - a) * ((f a + f b) / 2) := by
  dsimp only
  rw [integral_reciprocal_affine ha hab.le]
  obtain ⟨hl, hu⟩ := integral_inv_bounds ha hab
  have h1 := mul_le_mul_of_nonneg_left hl hβ
  have h2 := mul_le_mul_of_nonneg_left hu hβ
  constructor
  · rw [show (b - a) * (α + β / ((a + b) / 2)) =
        (b - a) * α + β * ((b - a) / ((a + b) / 2)) by ring]
    linarith only [h1]
  · rw [show (b - a) * ((α + β / a + (α + β / b)) / 2) =
        (b - a) * α + β * ((b - a) * ((1 / a + 1 / b) / 2)) by ring]
    linarith only [h2]

/-- Lemma 13 for a nonpositive reciprocal coefficient. -/
theorem hermite_hadamard_inv_nonpos {a b α β : ℝ}
    (ha : 0 < a) (hab : a < b) (hβ : β ≤ 0) :
    let f (r : ℝ) := α + β / r
    (b - a) * ((f a + f b) / 2) ≤ (∫ r in Icc a b, f r) ∧
      (∫ r in Icc a b, f r) ≤ (b - a) * f ((a + b) / 2) := by
  dsimp only
  rw [integral_reciprocal_affine ha hab.le]
  obtain ⟨hl, hu⟩ := integral_inv_bounds ha hab
  have h1 := mul_le_mul_of_nonpos_left hu hβ
  have h2 := mul_le_mul_of_nonpos_left hl hβ
  constructor
  · rw [show (b - a) * ((α + β / a + (α + β / b)) / 2) =
        (b - a) * α + β * ((b - a) * ((1 / a + 1 / b) / 2)) by ring]
    linarith only [h1]
  · rw [show (b - a) * (α + β / ((a + b) / 2)) =
        (b - a) * α + β * ((b - a) / ((a + b) / 2)) by ring]
    linarith only [h2]

/-- Comparing the endpoint values gives the sign of the reciprocal coefficient. -/
theorem reciprocal_affine_decreasing_iff {a b α β : ℝ} (ha : 0 < a) (hab : a < b) :
    α + β / b ≤ α + β / a ↔ 0 ≤ β := by
  have hb := ha.trans hab
  rw [← sub_nonneg]
  have heq : (α + β / a) - (α + β / b) = β * ((b - a) / (a * b)) := by
    field_simp [ha.ne', hb.ne']; ring
  rw [heq, mul_nonneg_iff_of_pos_right (div_pos (sub_pos.mpr hab) (mul_pos ha hb))]

end LeastPrime
