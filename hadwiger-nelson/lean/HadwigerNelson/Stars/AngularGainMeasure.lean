import HadwigerNelson.Stars.ScoreIntegrable
import HadwigerNelson.Stars.AngularGain
import Mathlib.MeasureTheory.Integral.Prod

namespace HadwigerNelson.Stars
open MeasureTheory Set
noncomputable section

variable {α : Type*} [MeasurableSpace α] {d : Nat}

theorem angleScore_lattice (W : Wave.Datum) (φ : Fin d → ℝ) (θ : ℝ) (z v : Plane)
    (hv : v ∈ Wave.lattice W) : angleScore W φ (z+v) θ = angleScore W φ z θ := by
  simp only [angleScore,add_right_comm z v,Wave.colour_periodic W _ v hv]

theorem measurable_angularGain (W : Wave.Datum) (φ : Fin d → ℝ) : Measurable (angularGain W φ) := by
  exact (measurable_angleScore (α := Plane × ℝ) W φ measurable_snd measurable_fst
    ).stronglyMeasurable.integral_prod_right'.measurable

theorem angularGain_range (W : Wave.Datum) (φ : Fin d → ℝ) (z : Plane) :
    0 ≤ angularGain W φ z ∧ angularGain W φ z ≤ d := by
  letI := Placement.uniformInterval_probability (show 0 < 2*Real.pi by positivity)
  have hi : Integrable (angleScore W φ z) (Placement.uniformInterval (2*Real.pi)) :=
    integrable_angleScore W φ measurable_id measurable_const
  refine ⟨integral_nonneg (fun θ => (localGain_range _ _).1),?_⟩
  simpa [angularGain] using integral_mono hi (integrable_const (d : ℝ))
    (fun θ => (localGain_range _ _).2)

theorem integrable_angularGain (W : Wave.Datum) (φ : Fin d → ℝ)
    (μ : Measure Plane) [IsFiniteMeasure μ] : Integrable (angularGain W φ) μ := by
  apply Integrable.of_bound (measurable_angularGain W φ).aestronglyMeasurable d
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (angularGain_range W φ z).1]
    exact (angularGain_range W φ z).2

end
end HadwigerNelson.Stars
