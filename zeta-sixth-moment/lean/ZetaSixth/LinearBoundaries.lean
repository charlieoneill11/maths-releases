import ZetaSixth.Regions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ZetaSixth

open Filter MeasureTheory

private theorem volume_planar_level (a b d : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p | a * p.1 + b * p.2 = d} = 0 := by
  have hs : MeasurableSet {p : ℝ × ℝ | a * p.1 + b * p.2 = d} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [Measure.volume_eq_prod ℝ ℝ]
  rcases h with ha | hb
  · rw [Measure.prod_apply_symm hs]
    have hf (y : ℝ) :
        (volume : Measure ℝ) ((fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | a * p.1 + b * p.2 = d}) = 0 := by
      apply measure_mono_null _ (measure_singleton ((d - b * y) / a))
      intro x hx
      change a * x + b * y = d at hx
      apply Set.mem_singleton_iff.mpr
      apply (eq_div_iff ha).mpr
      rw [mul_comm x a]
      linarith only [hx]
    simp_rw [hf, lintegral_zero]
  · rw [Measure.prod_apply hs]
    have hf (x : ℝ) :
        (volume : Measure ℝ) ((fun y : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | a * p.1 + b * p.2 = d}) = 0 := by
      apply measure_mono_null _ (measure_singleton ((d - a * x) / b))
      intro y hy
      change a * x + b * y = d at hy
      apply Set.mem_singleton_iff.mpr
      apply (eq_div_iff hb).mpr
      rw [mul_comm y b]
      linarith only [hy]
    simp_rw [hf, lintegral_zero]

/-- A nonconstant affine level set is null in the three-dimensional product volume. -/
theorem volume_coordinate_level (a b c d : ℝ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (volume : Measure Point) {p | a * p.1 + b * p.2.1 + c * p.2.2 = d} = 0 := by
  have hs : MeasurableSet {p : Point | a * p.1 + b * p.2.1 + c * p.2.2 = d} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  rcases h with ha | hbc
  · rw [Measure.prod_apply_symm hs]
    have hf (y : ℝ × ℝ) :
        (volume : Measure ℝ) ((fun x : ℝ => (x, y)) ⁻¹'
          {p : Point | a * p.1 + b * p.2.1 + c * p.2.2 = d}) = 0 := by
      apply measure_mono_null _ (measure_singleton ((d - b * y.1 - c * y.2) / a))
      intro x hx
      change a * x + b * y.1 + c * y.2 = d at hx
      apply Set.mem_singleton_iff.mpr
      apply (eq_div_iff ha).mpr
      rw [mul_comm x a]
      linarith only [hx]
    simp_rw [hf, lintegral_zero]
  · rw [Measure.prod_apply hs]
    have hf (x : ℝ) :
        (volume : Measure (ℝ × ℝ)) ((fun y : ℝ × ℝ => (x, y)) ⁻¹'
          {p : Point | a * p.1 + b * p.2.1 + c * p.2.2 = d}) = 0 := by
      have heq : (fun y : ℝ × ℝ => (x, y)) ⁻¹' {p : Point | a * p.1 + b * p.2.1 + c * p.2.2 = d}
          = {y | b * y.1 + c * y.2 = d - a * x} := by
        ext y
        change a * x + b * y.1 + c * y.2 = d ↔ b * y.1 + c * y.2 = d - a * x
        constructor <;> intro he <;> linarith only [he]
      rw [heq, volume_planar_level b c (d - a * x) hbc]
    simp_rw [hf, lintegral_zero]

/-- A nonconstant affine equation in the three ambient coordinates fails almost everywhere. -/
theorem ae_ne_coord_level (a b c d : ℝ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∀ᵐ p : Point ∂volume, a * p.1 + b * p.2.1 + c * p.2.2 ≠ d := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using volume_coordinate_level a b c d h

theorem ae_trace_ne (r : ℝ) : ∀ᵐ p : Point ∂volume, trace p ≠ r := by
  simpa only [trace, shortSum, one_mul] using ae_ne_coord_level 1 1 1 r (by norm_num)

end ZetaSixth
