import HadwigerNelson.Placement.Overlap
import HadwigerNelson.Placement.TwoTiles

/-! The blank probability of a partial wave (Lemma 8). -/

open MeasureTheory HadwigerNelson.Wave Set

namespace HadwigerNelson.Placement

noncomputable section

private theorem zeroPoint : point 0 0 = 0 := by ext i; fin_cases i <;> rfl

private theorem base_zero_region (W : Datum) : baseEvent W 0 0 ∩ rectangle W =
    Prod.swap ⁻¹' tileRegion W.left W.right H := by
  ext ⟨u,y⟩
  constructor
  · rintro ⟨⟨hc,_⟩,hu,hy⟩
    exact first_colour_in_rectangle W (point u y) (Ioc_subset_Icc_self hu) (Ioc_subset_Icc_self hy) hc
  · intro ht
    change point u y ∈ Wave.tile W at ht
    have hc := colour_on_tile W _ ht
    have hb := tile_coord_bounds W ht
    change (0 < u ∧ u < 1) ∧ (0 < y ∧ y < H) at hb
    refine ⟨⟨hc,?_⟩,⟨hb.1.1,?_⟩,⟨hb.2.1,?_⟩⟩
    · simpa only [zeroPoint, add_zero] using hc
    · change u ≤ 2*W.x
      linarith [hb.1.2, W.x_bounds.1]
    · change y ≤ 3*H
      linarith [hb.2.2,H_pos]

private theorem integral_right (W : Datum) : (∫ y in 0..H, W.right y) = W.x*H := by
  have hs (a b : ℝ) : IntervalIntegrable W.right volume a b := W.right_continuous.intervalIntegrable _ _
  have shift : Continuous (fun y : ℝ ↦ W.right (y+H/2)) := W.right_continuous.comp (continuous_id.add continuous_const)
  have he := intervalIntegral.integral_comp_add_right (a := 0) (b := H/2) W.right (H/2)
  rw [zero_add, show H/2+H/2 = H by ring] at he
  rw [← intervalIntegral.integral_add_adjacent_intervals (hs 0 (H/2)) (hs (H/2) H), ← he,
    ← intervalIntegral.integral_add (hs 0 (H/2)) (shift.intervalIntegrable _ _)]
  simp_rw [W.complement]
  rw [intervalIntegral.integral_const]
  simp <;> ring

/-- Complementarity of the two profile halves fixes the mean upper boundary at `x`. The
remaining blank area is given by the integral of the lower boundary. -/
theorem blankDensity_eq_integral (W : Datum) : blankDensity W = (∫ y in 0..H, W.left y) / (W.x*H) := by
  let T := tileRegion W.left W.right H
  have hm : MeasurableSet T := measurableSet_regionBetween W.left_continuous.measurable
    W.right_continuous.measurable measurableSet_Ioo
  have harea : ((volume : Measure ℝ).prod volume).real T = W.x*H - ∫ y in 0..H, W.left y := by
    have ev := volume_regionBetween_eq_integral (μ := (volume : Measure ℝ))
      (W.left_continuous.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (W.right_continuous.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (measurableSet_Ioo (a := 0) (b := H))
      (fun y _ ↦ by linarith [(W.left_bounds y).2,(W.right_bounds y).1])
    have hpos : 0 ≤ ∫ y in Ioo 0 H, (W.right-W.left) y := by
      apply setIntegral_nonneg measurableSet_Ioo
      intro y _; change 0 ≤ W.right y - W.left y
      linarith [(W.left_bounds y).2,(W.right_bounds y).1]
    rw [Measure.real,show (volume : Measure ℝ).prod volume T = _ from ev, ENNReal.toReal_ofReal hpos,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le H_pos.le]
    change (∫ y in 0..H, W.right y-W.left y) = _
    rw [intervalIntegral.integral_sub (W.right_continuous.intervalIntegrable ..) (W.left_continuous.intervalIntegrable ..),integral_right]
  have hs : directionalMonoProb W (point 0 0) =
      6*((2*W.x)⁻¹ * (3*H)⁻¹) * (W.x*H - ∫ y in 0..H, W.left y) := by
    rw [monoProb_eq_six, baseProbability_rect, base_zero_region,
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).measureReal_preimage hm.nullMeasurableSet,
      harea]
    ring
  have addone : blankDensity W + directionalMonoProb W (point 0 0) = 1 := by
    have hb : Integrable (fun t : Translation ↦ if Wave.colour W (point t.1 t.2) = none then (1:ℝ) else 0)
        (translationLaw W) := by
      apply ((integrable_const (μ := translationLaw W) (1:ℝ)).indicator
        ((Wave.blank_closed W).measurableSet.preimage continuous_translationPoint.measurable)).congr
      exact Filter.Eventually.of_forall fun t ↦ by
        simp only [Set.indicator,Set.mem_preimage,Set.mem_setOf_eq,translationPoint]
    have hi : Integrable (fun t : Translation ↦ sameColour W (point t.1 t.2) (point t.1 t.2 + point 0 0)) (translationLaw W) :=
      integrable_sameColour (μ := translationLaw W) W continuous_translationPoint.measurable
      (continuous_translationPoint.add (continuous_const (y := point 0 0))).measurable
    unfold blankDensity directionalMonoProb
    rw [← integral_add hb hi]
    have eq (t : Translation) : (if Wave.colour W (point t.1 t.2) = none then (1:ℝ) else 0) +
        sameColour W (point t.1 t.2) (point t.1 t.2 + point 0 0) = 1 := by
      cases h : Wave.colour W (point t.1 t.2) <;> simp [h,sameColour,zeroPoint]
    simp_rw [eq]
    simp
  rw [hs] at addone
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  field_simp [hx.ne',H_pos.ne'] at addone ⊢
  linarith

end
end HadwigerNelson.Placement
