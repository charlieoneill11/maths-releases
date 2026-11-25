import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Real
import HadwigerNelson.Placement.Regions
import HadwigerNelson.Wave.Geometry.Halves
import Mathlib.MeasureTheory.Group.Prod

/-! Coordinate reflections of the tile covariogram, Lemma 9. -/

open MeasureTheory HadwigerNelson.Wave Set

namespace HadwigerNelson.Placement

noncomputable section

theorem measurable_overlap (W : Datum) (u v : ℝ) :
    MeasurableSet (overlapRegion W.left W.right H u v) := by
  have hm : MeasurableSet (tileRegion W.left W.right H) :=
    measurableSet_regionBetween W.left_continuous.measurable W.right_continuous.measurable measurableSet_Ioo
  exact hm.inter (hm.preimage (by fun_prop))

/-- A horizontal width bound and the wave height bound the support of its covariogram. -/
theorem overlapRegion_eq_empty_of_outside (W : Datum) {R u v : ℝ}
    (hR : ∀ y ∈ Ioo 0 H, W.right y ≤ R) (hout : R ≤ |u| ∨ H ≤ |v|) :
    overlapRegion W.left W.right H u v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨y,x⟩ ⟨ha,hb⟩
  change (0 < y ∧ y < H) ∧ W.left y < x ∧ x < W.right y at ha
  change (0 < y-v ∧ y-v < H) ∧ W.left (y-v) < x-u ∧ x-u < W.right (y-v) at hb
  have hx₀ : 0 < x := (W.left_bounds _).1.trans_lt ha.2.1
  have hx₁ : x < R := ha.2.2.trans_le (hR _ ha.1)
  have hu₀ : 0 < x-u := (W.left_bounds _).1.trans_lt hb.2.1
  have hu₁ : x-u < R := hb.2.2.trans_le (hR _ hb.1)
  rcases hout with hu | hv
  · exact (not_lt_of_ge hu) (abs_lt.mpr ⟨by linarith,by linarith⟩)
  · exact (not_lt_of_ge hv) (abs_lt.mpr ⟨by linarith [ha.1.1,hb.1.2],by linarith [ha.1.2,hb.1.1]⟩)

theorem tileCovariogram_zero_of_outside (W : Datum) {R u v : ℝ}
    (hR : ∀ y ∈ Ioo 0 H, W.right y ≤ R) (hout : R ≤ |u| ∨ H ≤ |v|) :
    tileCovariogram W.left W.right H u v = 0 := by
  simp [tileCovariogram, overlapRegion_eq_empty_of_outside W hR hout]

private theorem tile_reflect (W : Datum) (y x : ℝ) :
    (H-y,x) ∈ tileRegion W.left W.right H ↔ (y,x) ∈ tileRegion W.left W.right H :=
  Wave.mem_tile_sigma1 W (point x y)

/-- Negating both coordinates exchanges the roles of the two intersecting tiles. -/
theorem tileCovariogram_neg (W : Datum) (u v : ℝ) :
    tileCovariogram W.left W.right H (-u) (-v) = tileCovariogram W.left W.right H u v := by
  let C := overlapRegion W.left W.right H u v
  have h : (fun z : ℝ × ℝ ↦ z + (v,u)) ⁻¹' C = overlapRegion W.left W.right H (-u) (-v) := by
    ext ⟨y,x⟩
    simp [C, overlapRegion, and_comm]
  have hp : MeasurePreserving (fun z : ℝ × ℝ ↦ z + (v,u)) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_add_right (volume : Measure ℝ) v).prod (measurePreserving_add_right volume u)
  have ht := hp.measureReal_preimage (measurable_overlap W u v).nullMeasurableSet
  change ((volume : Measure ℝ).prod volume).real _ = ((volume : Measure ℝ).prod volume).real C
  rw [← h]; exact ht

/-- Reflecting the vertical coordinate around height `H/2` preserves the open tile. -/
theorem tileCovariogram_neg_y (W : Datum) (u v : ℝ) :
    tileCovariogram W.left W.right H u (-v) = tileCovariogram W.left W.right H u v := by
  let F : ℝ × ℝ → ℝ × ℝ := Prod.map (fun y : ℝ ↦ H-y) id
  have hp : MeasurePreserving F ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    have hn : MeasurePreserving (fun y : ℝ ↦ -y) volume volume :=
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).measurePreserving
    have hr : MeasurePreserving (fun y : ℝ ↦ H-y) volume volume := by
      simpa only [Function.comp_def,sub_eq_add_neg] using (measurePreserving_add_left volume H).comp hn
    exact hr.prod (MeasurePreserving.id volume)
  have h : F ⁻¹' (overlapRegion W.left W.right H u v) = overlapRegion W.left W.right H u (-v) := by
    ext ⟨y,x⟩
    change ((H-y,x) ∈ tileRegion _ _ _ ∧ (H-y-v,x-u) ∈ tileRegion _ _ _) ↔
      (y,x) ∈ tileRegion _ _ _ ∧ (y- -v,x-u) ∈ tileRegion _ _ _
    rw [tile_reflect, show H-y-v = H-(y- -v) by ring, tile_reflect]
  have ht := hp.measureReal_preimage (measurable_overlap W u v).nullMeasurableSet
  simpa only [tileCovariogram,h] using ht

theorem tileCovariogram_abs (W : Datum) (u v : ℝ) :
    tileCovariogram W.left W.right H u v = tileCovariogram W.left W.right H |u| |v| := by
  have hx (x y : ℝ) : tileCovariogram W.left W.right H (-x) y = tileCovariogram W.left W.right H x y := by
    rw [← tileCovariogram_neg_y W (-x) y, tileCovariogram_neg]
  rcases le_or_gt 0 u with hu | hu <;> rcases le_or_gt 0 v with hv | hv <;>
    simp [abs_of_nonneg,abs_of_neg,hu,hv,hx,tileCovariogram_neg_y]

end
end HadwigerNelson.Placement
