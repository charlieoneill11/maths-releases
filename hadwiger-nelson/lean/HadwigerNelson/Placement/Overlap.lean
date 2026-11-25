import HadwigerNelson.Placement.Regions
import HadwigerNelson.Placement.Slice
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! The covariogram of a tile as the Lebesgue area of intersecting horizontal slices. -/

open MeasureTheory Set

namespace HadwigerNelson.Placement

noncomputable section

/-- Fubini's theorem identifies the actual area with `sliceArea`, including disjoint tiles. -/
theorem tileCovariogram_eq_sliceArea {left right : ℝ → ℝ} {H D δ : ℝ}
    (hl : Continuous left) (hr : Continuous right) (hδ : 0 ≤ δ) :
    tileCovariogram left right H D δ = sliceArea left right H D δ := by
  let T := tileRegion left right H
  let overlap := T ∩ (fun z : ℝ × ℝ ↦ (z.1 - δ, z.2 - D)) ⁻¹' T
  change ((volume : Measure ℝ).prod volume).real overlap = _
  by_cases h : H ≤ δ
  · have he : overlap = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨y,x⟩ ⟨⟨⟨_,hy⟩,_⟩,⟨⟨hd,_⟩,_⟩⟩
      change y < H at hy
      change 0 < y - δ at hd
      linarith
    simp [he, sliceArea, h]
  have hδH : δ ≤ H := le_of_not_ge h
  let low := fun y ↦ max (left y) (left (y-δ) + D)
  let high := fun y ↦ min (right y) (right (y-δ) + D)
  let cap := fun y ↦ max (low y) (high y)
  have he : overlap = regionBetween low cap (Ioo δ H) := by
    ext ⟨y,x⟩
    change ((0 < y ∧ y < H) ∧ left y < x ∧ x < right y) ∧
      ((0 < y - δ ∧ y - δ < H) ∧ left (y-δ) < x-D ∧ x-D < right (y-δ)) ↔
      (δ < y ∧ y < H) ∧ low y < x ∧ x < cap y
    simp only [low, high, cap, max_lt_iff, lt_max_iff, lt_min_iff]
    constructor
    · rintro ⟨⟨⟨_,hy⟩,ha,hb⟩,⟨⟨hd,_⟩,hc,he'⟩⟩
      refine ⟨⟨by linarith,hy⟩,⟨ha,by linarith⟩,Or.inr ⟨hb,by linarith⟩⟩
    · rintro ⟨⟨ha,hb⟩,⟨hc,hd⟩,(he'|⟨hf,hg⟩)⟩
      · exact he'.elim (fun hlt ↦ (not_lt_of_ge hc.le hlt).elim) (fun hlt ↦ (not_lt_of_ge hd.le hlt).elim)
      · exact ⟨⟨⟨by linarith,hb⟩,hc,hf⟩,⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩⟩
  have cl : Continuous low := by dsimp [low]; fun_prop
  have cc : Continuous cap := by dsimp [cap, high]; fun_prop
  have hf : ((volume : Measure ℝ).prod volume) overlap =
      ENNReal.ofReal (∫ y in Ioo δ H, (cap - low) y) := by
    rw [he]
    exact volume_regionBetween_eq_integral
      (cl.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (cc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      measurableSet_Ioo (fun _ _ ↦ le_max_left _ _)
  have hv (y : ℝ) : (cap - low) y = sliceLength left right D δ y := by
    change max (low y) (high y) - low y = max 0 (high y - low y)
    rw [← max_sub_sub_right, sub_self]
  have hp : 0 ≤ ∫ y in Ioo δ H, (cap - low) y :=
    setIntegral_nonneg measurableSet_Ioo (fun y _ ↦ sub_nonneg.mpr (le_max_left _ _))
  rw [Measure.real, hf, ENNReal.toReal_ofReal hp, sliceArea, if_neg h,
    intervalIntegral.integral_of_le hδH, integral_Ioc_eq_integral_Ioo]
  simp_rw [hv]

end
end HadwigerNelson.Placement
