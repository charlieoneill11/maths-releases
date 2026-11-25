import HadwigerNelson.Wave.Holes.Placement
import HadwigerNelson.Wave.Holes.Lower

namespace HadwigerNelson.Wave
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory Set

/-- Lemma 17. The holes are symmetric in both coordinates. Horizontal slices
give the overlap integral and the two lattice alignments give disjoint
families of favourable translations. -/
theorem hole_covariogram_bounds (W : Datum) :
    (∀ u v : Plane, |u 0| ≤ |v 0| → |u 1| ≤ |v 1| →
      holeCovariogram W v ≤ holeCovariogram W u) ∧
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → holeCovariogram W (point x y) =
      ∫ t in Ioc (y - W.y0) W.y0, holeSlice (W.left t) (W.left (t-y)) x) ∧
    (∀ v : Plane, max (holeCovariogram W v) (holeCovariogram W (v-point 0 1)) /
      (2*W.x*H) ≤ bothBlank W v) := by
  exact ⟨holeCovariogram_antitone W, hole_horizontal_formula W, bothBlank_max_lower W⟩

/-- Lemma 19 permits any refinement of the merged knot list. -/
theorem holeLower_sound {k : ℕ} (W : Datum) (x y : ℝ) (grid : Fin (k+1) → ℝ)
    (hg : tickUp y < 2*W.y0 → holePartition W (tickUp y) grid)
    (v : Plane) (hx : |v 0| ≤ x) (hy : |v 1| ≤ y) :
    0 ≤ holeLower W x y grid ∧ holeLower W x y grid ≤ holeCovariogram W v / (2*W.x*H) := by
  exact holeLower_bound W x y grid hg v hx hy

end
end HadwigerNelson.Wave
