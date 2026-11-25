import Chowla.Model.Extremal

namespace Chowla

open MeasureTheory Set

/-- The Gaussian part of the covariance of two rectangle profiles. -/
theorem rectanglePair_gaussian {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (2 * ∫ u : ℝ, |u| * rectangle a u * rectangle b u) = 2 * min a b ^ 2 := by
  let c := min a b
  have hc : 0 ≤ c := le_min ha hb
  have hf : (fun u : ℝ => |u| * rectangle a u * rectangle b u) =
      (Icc (-c) c).indicator (fun u => |u|) := by
    funext u
    have hmem : u ∈ Icc (-c) c ↔ u ∈ Icc (-a) a ∧ u ∈ Icc (-b) b := by
      simp only [mem_Icc, c, neg_le, le_min_iff]
      tauto
    by_cases ha' : u ∈ Icc (-a) a <;> by_cases hb' : u ∈ Icc (-b) b <;>
      simp [rectangle, hmem, ha', hb']
  have hc₁ : -c ≤ 0 := neg_nonpos.mpr hc
  have hl : (∫ u in -c..0, |u|) = -(∫ u in -c..0, u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    exact abs_of_nonpos ((mem_Icc.mp (by rwa [uIcc_of_le hc₁] at hu : u ∈ Icc (-c) 0)).2)
  have hr : (∫ u in 0..c, |u|) = ∫ u in 0..c, u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact abs_of_nonneg ((mem_Icc.mp (by rwa [uIcc_of_le hc] at hu : u ∈ Icc 0 c)).1)
  rw [hf, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -c ≤ c from hc₁.trans hc),
    ← intervalIntegral.integral_add_adjacent_intervals
      (continuous_abs.intervalIntegrable _ _) (continuous_abs.intervalIntegrable _ _),
    hl, hr, integral_id, integral_id]
  dsimp only [c]
  ring

end Chowla
