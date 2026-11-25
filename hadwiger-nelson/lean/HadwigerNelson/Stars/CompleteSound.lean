import HadwigerNelson.Stars.CompleteGain
import HadwigerNelson.Stars.SourceGain

namespace HadwigerNelson.Stars.BoxCheck

/-- The complete-wave credit checker, together with its separately checked layout,
bounds the expected gain at every vertex of the specified unit segments. -/
theorem complete_gain_of_check (layout : checkSourceBoxes = true) (tests : checkComplete = true)
    (E : Finset (Plane × Plane)) (unit : ∀ e ∈ E, dist e.1 e.2=1) (v : Plane) :
    (8/10^9 : ℝ) * degree E v ≤
      ∫ ω, gain E (Proof.placedColours Wave.completeDatum ω) v ∂Placement.law Wave.completeDatum := by
  refine complete_gain_of_boxes layout tests ?_ ?_ E unit v
  · intro d hd _
    exact harmonic_source_gain layout hd
  · intro d hd
    exact saturated_source_gain layout (by omega)

end HadwigerNelson.Stars.BoxCheck
