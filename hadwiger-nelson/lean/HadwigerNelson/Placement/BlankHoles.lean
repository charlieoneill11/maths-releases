import HadwigerNelson.Wave.Geometry.Null
import HadwigerNelson.Placement.Blank

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set
noncomputable section

theorem placed_blank_in_holes (W : Wave.Datum) (θ : ℝ) (x : Plane) :
    ∀ᵐ t ∂translationLaw W, colour W (θ,t) x = none → place (θ,t) x ∈ Wave.holeCopies W := by
  have preserve := (measurePreserving_add_left (volume : Measure Plane) (rotate θ x)).comp
    translationPoint_preserves_volume
  have null := (translationLaw_ac W) (preserve.quasiMeasurePreserving.preimage_null (Wave.blank_diff_holes_null W))
  rw [ae_iff]
  convert null using 2
  ext t
  change (¬(Wave.colour W (place (θ,t) x) = none → place (θ,t) x ∈ Wave.holeCopies W)) ↔
    Wave.colour W (place (θ,t) x) = none ∧ place (θ,t) x ∉ Wave.holeCopies W
  tauto

end
end HadwigerNelson.Forest
