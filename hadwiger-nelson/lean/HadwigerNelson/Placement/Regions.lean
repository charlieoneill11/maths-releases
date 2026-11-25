import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Euclidean areas of the tile intersections in the wave covariogram. -/

open MeasureTheory Set

namespace HadwigerNelson.Placement

noncomputable section

/-- Coordinates are ordered `(height, horizontal position)` for Fubini's theorem. -/
def tileRegion (left right : ℝ → ℝ) (H : ℝ) : Set (ℝ × ℝ) :=
  regionBetween left right (Ioo 0 H)

/-- Intersection of a tile and the tile translated by `(D,δ)` in physical coordinates. -/
def overlapRegion (left right : ℝ → ℝ) (H D δ : ℝ) : Set (ℝ × ℝ) :=
  let T := tileRegion left right H
  T ∩ (fun z ↦ (z.1 - δ, z.2 - D)) ⁻¹' T

def tileCovariogram (left right : ℝ → ℝ) (H D δ : ℝ) : ℝ :=
  ((volume : Measure ℝ).prod volume).real (overlapRegion left right H D δ)

end
end HadwigerNelson.Placement
