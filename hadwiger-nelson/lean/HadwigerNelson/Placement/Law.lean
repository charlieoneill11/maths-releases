import HadwigerNelson.Placement.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Definition 7. All averages in this file are taken over physical rotations and translations. -/

open MeasureTheory Set
open scoped ENNReal

namespace HadwigerNelson.Placement

noncomputable section

theorem integral_uniformInterval {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ) :
    (∫ x, f x ∂uniformInterval T) = T⁻¹ * ∫ x in 0..T, f x := by
  rw [uniformInterval, integral_smul_measure, intervalIntegral.integral_of_le hT.le]
  simp [ENNReal.toReal_ofReal hT.le]

def blankDensity (W : Wave.Datum) : ℝ :=
  ∫ t, if Wave.colour W (Wave.point t.1 t.2) = none then 1 else 0 ∂translationLaw W

def directionalMonoProb (W : Wave.Datum) (e : Plane) : ℝ :=
  ∫ t, sameColour W (Wave.point t.1 t.2) (Wave.point t.1 t.2 + e) ∂translationLaw W

def meanMonoProb (W : Wave.Datum) : ℝ :=
  ∫ θ, directionalMonoProb W (Wave.point (Real.cos θ) (Real.sin θ)) ∂uniformInterval (2 * Real.pi)

end
end HadwigerNelson.Placement
