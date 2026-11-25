import HadwigerNelson.Angular.Datum
import HadwigerNelson.Placement.Blank
import HadwigerNelson.Wave.Geometry.Null

namespace HadwigerNelson.Wave
open MeasureTheory

/-- A fixed vertex almost surely avoids the null boundary of the complete wave. -/
theorem complete_ae_nonblank (v : Plane) :
    ∀ᵐ ω ∂Placement.law completeDatum, (Placement.colour completeDatum ω v).isSome = true := by
  exact Placement.placed_nonblank_ae completeDatum v
    (blank_volume_zero completeDatum (funext completeDatum_left))

end HadwigerNelson.Wave
