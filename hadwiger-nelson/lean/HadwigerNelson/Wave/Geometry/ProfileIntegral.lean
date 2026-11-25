import HadwigerNelson.Wave.Geometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace HadwigerNelson.Wave
open MeasureTheory Set
noncomputable section

/-- A whole period has exactly twice the area of the nonzero lower profile. -/
theorem integral_left_support (W : Datum) :
    (∫ y in 0..H, W.left y) = 2 * ∫ y in 0..W.y0, W.left y := by
  have hi (a b : ℝ) := W.left_continuous.intervalIntegrable (μ:=volume) a b
  have vanish : (∫ y in W.y0..H/2, W.left y)=0 := by
    calc
      _ = ∫ _ in W.y0..H/2, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        exact W.left_zero z (by rwa [uIcc_of_le (by linarith [W.y0_bounds.2,H_pos])] at hz)
      _ = _ := by simp
  have split := intervalIntegral.integral_add_adjacent_intervals (hi 0 W.y0) (hi W.y0 (H/2))
  have mid := intervalIntegral.integral_comp_sub_left (a:=0) (b:=H/2) W.left H
  rw [show H-H/2=H/2 by ring,sub_zero] at mid
  simp_rw [W.left_periodic.sub_eq',W.left_even] at mid
  have outer := intervalIntegral.integral_add_adjacent_intervals (hi 0 (H/2)) (hi (H/2) H)
  linarith

/-- The interval occupied by the hole has the same total width integral
as the complete period. -/
theorem integral_left_hole_interval (W : Datum) :
    (∫ y in -W.y0..W.y0, W.left y) = ∫ y in 0..H, W.left y := by
  have half := intervalIntegral.integral_comp_neg (a:=0) (b:=W.y0) W.left
  simp only [W.left_even,neg_zero] at half
  have whole := intervalIntegral.integral_add_adjacent_intervals
    (W.left_continuous.intervalIntegrable (μ:=volume) (-W.y0) 0)
    (W.left_continuous.intervalIntegrable (μ:=volume) 0 W.y0)
  rw [integral_left_support]
  linarith

end
end HadwigerNelson.Wave
