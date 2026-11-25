import HadwigerNelson.Placement.Class
import Mathlib.Tactic.FieldSimp

namespace HadwigerNelson.Placement
open MeasureTheory
noncomputable section

/-- The last step of Lemma 10. Reflection across the vertical axis and
half-turn invariance reduce a full angular integral to the first quadrant. -/
theorem integral_four_quadrants (f : ℝ → ℝ)
    (hint : ∀ a b, IntervalIntegrable f volume a b)
    (hh : ∀ t, f (t + Real.pi) = f t)
    (hr : ∀ t, f (Real.pi - t) = f t) :
    (∫ t in 0..2*Real.pi, f t) = 4 * ∫ t in 0..Real.pi/2, f t := by
  have half : (∫ t in Real.pi..2*Real.pi, f t) = ∫ t in 0..Real.pi, f t := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi) f Real.pi
    simpa only [hh, zero_add, two_mul] using h.symm
  have quarter : (∫ t in Real.pi/2..Real.pi, f t) = ∫ t in 0..Real.pi/2, f t := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi/2) f Real.pi
    rw [show Real.pi - Real.pi/2 = Real.pi/2 by ring, sub_zero] at h
    simpa only [hr] using h.symm
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 Real.pi) (hint Real.pi (2*Real.pi))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 (Real.pi/2)) (hint (Real.pi/2) Real.pi)
  linarith [half, quarter]

/-- The angular observable is integrable on every finite interval: it is the
translation integral of a bounded measurable zero-one function. -/
theorem intervalIntegrable_direction (W : Wave.Datum) (a b : ℝ) :
    IntervalIntegrable (fun θ => directionalMonoProb W (Wave.point (Real.cos θ) (Real.sin θ)))
      volume a b := by
  have hd : Measurable (fun θ : ℝ => Wave.point (Real.cos θ) (Real.sin θ)) :=
    (continuous_point Real.continuous_cos Real.continuous_sin).measurable
  exact ⟨integrable_directional (volume.restrict (Set.Ioc a b)) W hd,
    integrable_directional (volume.restrict (Set.Ioc b a)) W hd⟩

/-- Apply the quadrant reduction to the physical probability of an equal-colour pair. -/
theorem meanMonoProb_quadrant (W : Wave.Datum) :
    meanMonoProb W = (2 / Real.pi) *
      ∫ θ in 0..Real.pi/2, directionalMonoProb W (Wave.point (Real.cos θ) (Real.sin θ)) := by
  let f := fun θ => directionalMonoProb W (Wave.point (Real.cos θ) (Real.sin θ))
  have signs := directional_signs W
  have hhalf (t : ℝ) : f (t + Real.pi) = f t := by
    unfold f
    rw [signs, signs (Real.cos t) (Real.sin t)]
    simp
  have hreflect (t : ℝ) : f (Real.pi - t) = f t := by
    unfold f
    rw [signs, signs (Real.cos t) (Real.sin t)]
    simp
  change (∫ θ, f θ ∂uniformInterval (2*Real.pi)) = _
  rw [integral_uniformInterval (by linarith [Real.pi_pos]), integral_four_quadrants f (intervalIntegrable_direction W) hhalf hreflect]
  change (2*Real.pi)⁻¹ * (4 * _) = (2 / Real.pi) * _
  ring

end
end HadwigerNelson.Placement
