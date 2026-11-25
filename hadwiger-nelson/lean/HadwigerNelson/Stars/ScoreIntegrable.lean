import HadwigerNelson.Stars.ScoreMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace HadwigerNelson.Stars
open MeasureTheory Set
noncomputable section

variable {α : Type*} [MeasurableSpace α] {d : Nat}

theorem integrable_angleScore (W : Wave.Datum) (φ : Fin d → ℝ)
    {μ : Measure α} [IsFiniteMeasure μ] {θ : α → ℝ} {z : α → Plane}
    (hθ : Measurable θ) (hz : Measurable z) :
    Integrable (fun a => angleScore W φ (z a) (θ a)) μ := by
  apply Integrable.of_bound (measurable_angleScore W φ hθ hz).aestronglyMeasurable d
  exact Filter.Eventually.of_forall fun a => by
    obtain ⟨lo,hi⟩ := localGain_range (Wave.colour W (z a))
      (fun j => Wave.colour W (z a + direction (θ a + φ j)))
    simpa only [angleScore,Real.norm_eq_abs,abs_of_nonneg lo] using hi

end
end HadwigerNelson.Stars
