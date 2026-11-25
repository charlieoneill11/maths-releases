import HadwigerNelson.Wave.Geometry.Seams
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace HadwigerNelson.Wave
open MeasureTheory

noncomputable section

private theorem graphLine_null (a b : ℝ) : volume (graphLine a b : Set Plane) = 0 := by
  apply Measure.addHaar_affineSubspace
  intro eq
  have h : point (b+1) 0 ∈ graphLine a b := by rw [eq]; trivial
  change b+1 = a*0+b at h
  linarith

private theorem horizontalLine_null (b : ℝ) : volume (horizontalLine b : Set Plane) = 0 := by
  apply Measure.addHaar_affineSubspace
  intro eq
  have h : point 0 (b+1) ∈ horizontalLine b := by rw [eq]; trivial
  change b+1=b at h
  linarith

theorem seams_volume_zero (W : Datum) : volume (seams W) = 0 := by
  have vert : volume (verticalSupports W) = 0 := measure_iUnion_null (fun _ => graphLine_null ..)
  have horiz : volume horizontalSupports = 0 :=
    measure_iUnion_null fun _ => measure_iUnion_null fun _ => horizontalLine_null _
  have segs : volume (seamSupports W) = 0 :=
    measure_iUnion_null fun _ => measure_iUnion_null fun _ =>
      measure_iUnion_null fun _ => measure_iUnion_null fun _ => graphLine_null ..
  exact measure_mono_null (seams_subset_supports W) (measure_union_null vert (measure_union_null horiz segs))

/-- The ambiguity outside the closed hole copies has zero planar measure. -/
theorem blank_diff_holes_null (W : Datum) :
    volume ({z | colour W z = none} \ holeCopies W) = 0 := by
  refine measure_mono_null ?_ (seams_volume_zero W)
  rintro z ⟨hz,hn⟩
  exact (blank_subset_holes_seams W hz).resolve_left hn

/-- Complete waves have no blank area, including all column walls, horizontal
row lines, and piecewise-affine interfaces. -/
theorem blank_volume_zero (W : Datum) (hl : W.left = fun _ => 0) :
    volume {z | colour W z = none} = 0 := by
  refine measure_mono_null ?_ (seams_volume_zero W)
  intro z hz
  rcases blank_subset_holes_seams W hz with h | h
  · obtain ⟨i,j,hi⟩ := h
    have ht := hi.2
    change |z 0-2*W.x*i| ≤ _ at ht
    rw [hl] at ht
    exact Or.inl ⟨i,sub_eq_zero.mp (abs_nonpos_iff.mp ht)⟩
  · exact h

end
end HadwigerNelson.Wave
