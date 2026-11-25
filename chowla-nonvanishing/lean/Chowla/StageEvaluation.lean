import Chowla.CheckerGram
import Chowla.Model.RowRefinement
import Chowla.StageCentral
import Chowla.StageGram
import Chowla.StageRows

namespace Chowla.Checker

/-- The cached evaluator computes the exact mixed and within-stage Gram sums. -/
theorem gramIncrease_model (old new : Array GridRow)
    (ho : ∀ r ∈ old.toList, GridRow.Valid r)
    (hn : ∀ r ∈ new.toList, GridRow.Valid r) :
    (gramIncrease old new : ℝ) =
      2 * inner (modelRows old) (modelRows new) + inner (modelRows new) (modelRows new) := by
  have hpair {a b : GridRow} (ha : a.Valid) (hb : b.Valid) :
      (gramGrid a b : ℝ) = innerRow a.modelRow b.modelRow := by
    have h := gramGrid_eq_innerRow a.rowData b.rowData ha.2 hb.2
    rw [ha.1, hb.1] at h
    exact h
  have hmem (A : Array GridRow) (i : Fin A.size) : A[i] ∈ A.toList :=
    Array.getElem_mem_toList i.isLt
  exact gramIncrease_sound old new GridRow.modelRow
    (fun i j => hpair (hn _ (hmem new i)) (ho _ (hmem old j)))
    (fun i j => hpair (hn _ (hmem new i)) (hn _ (hmem new j)))

private theorem gramIncrease_prepared (old new : List Rows.RowData)
    (ho : old.all Rows.RowData.validWidths = true)
    (hn : new.all Rows.RowData.validWidths = true) :
    (gramIncrease (prepareRows old) (prepareRows new) : ℝ) =
      2 * inner (old.map Rows.RowData.toRow) (new.map Rows.RowData.toRow) +
        inner (new.map Rows.RowData.toRow) (new.map Rows.RowData.toRow) := by
  simpa only [prepareRows_modelRows] using gramIncrease_model (prepareRows old) (prepareRows new)
    (fun _ hr => prepareRows_valid ho hr) (fun _ hr => prepareRows_valid hn hr)

set_option maxRecDepth 8192 in
/-- The first stage combines its real central enclosure with the upper bound
obtained by rounding individual sets of Gram entries towards positive infinity. -/
theorem stageOneBounds_sound : (stageOneBounds ()).Sound 0 := by
  have hF : (Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2).map Rows.RowData.toRow =
      stageAmplitude 0 := rfl
  have hcentral := stageOneCentral_encloses
  dsimp only at hcentral
  have hc := stageOne_refine_inner_G []
  simp only [List.append_nil, hF] at hc
  rw [hc] at hcentral
  have hround := stageOne_rounding_upper (prepareRows stageOneLinear) (prepareRows stageOneQuadratic)
  have hcast := (Rat.cast_le (K := ℝ)).mpr hround
  rw [Rat.cast_add] at hcast
  rw [gramIncrease_prepared _ _ stageOneQuadratic_validWidths stageOneLinear_validWidths] at hcast
  have hquad := gramIncrease_model #[] (prepareRows stageOneQuadratic)
    (fun _ hr => by simp at hr) (fun _ hr => prepareRows_valid stageOneQuadratic_validWidths hr)
  simp only [prepareRows_modelRows, show modelRows #[] = [] from rfl] at hquad
  rw [hquad] at hcast
  have hrefine := stageOne_refine_gram [] (by simpa only [List.append_nil] using stageOneRows_validWidths)
  simp only [List.append_nil, hF] at hrefine
  have hadd (A B : Amplitude) : inner (A ++ B) (A ++ B) =
      (2 * inner B A + inner A A) + (2 * inner [] B + inner B B) := by
    simp only [inner_append_left, inner_append_right, show inner [] B = 0 from rfl, mul_zero, zero_add]
    rw [inner_comm A B]
    ring
  have hmodel := hrefine.symm
  rw [List.map_append, hadd] at hmodel
  change _ ≤ inner_G (stageAmplitude 0) ∧ inner_G (stageAmplitude 0) ≤ _ ∧
    inner (stageAmplitude 0) (stageAmplitude 0) ≤ _
  rw [hmodel]
  exact ⟨hcentral.1, hcentral.2, hcast⟩

private def additionalEarlyRows (n : ℕ) : List Rows.RowData :=
  (if 2 ≤ n then Rows.r3 else []) ++ (if 3 ≤ n then Rows.r4 else []) ++
    (if 4 ≤ n then Rows.r5 else [])

private theorem firstFourRows_split (n : ℕ) :
    firstFourRows n = stageOneLinear ++ stageOneQuadratic ++ additionalEarlyRows n := by
  simp only [firstFourRows, additionalEarlyRows, List.append_assoc]

private theorem initialStageRows_split (n : ℕ) :
    initialStageRows n = (Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++
        additionalEarlyRows n := by
  simp only [initialStageRows, additionalEarlyRows, List.append_assoc]

private theorem stageAmplitude_early (i : Fin 8) (hi : i.val < 4) :
    stageAmplitude i = (initialStageRows (i.val + 1)).map Rows.RowData.toRow := by
  simp only [stageAmplitude, stageRows, if_pos hi]

private theorem earlyStep_sound (i j : Fin 8) (hi : i.val < 4) (hj : j.val < 4)
    (previous : StageBounds) (new : List Rows.RowData)
    (hs : previous.Sound i) (hc : previous.check i = true)
    (hrows : initialStageRows (j.val + 1) = initialStageRows (i.val + 1) ++ new)
    (hn : new.all Rows.RowData.validWidths = true) :
    (earlyBounds i previous (prepareRows (firstFourRows (i.val + 1))) (prepareRows new)).Sound j := by
  have hcenter := centralRows_encloses_inner_G new hn
  have hgram := gramIncrease_prepared _ _ (firstFourRows_validWidths (i.val + 1)) hn
  have hrefine := stageOne_refine_inner (additionalEarlyRows (i.val + 1)) _ (rows_isAmplitude hn)
  rw [← firstFourRows_split, ← initialStageRows_split, ← stageAmplitude_early i hi] at hrefine
  rw [hrefine] at hgram
  apply earlyBounds_sound i j hi hj previous _ _ _ hs hc _ hcenter.1 hcenter.2 hgram
  rw [stageAmplitude_early j hj, hrows, List.map_append, ← stageAmplitude_early i hi]

private theorem map_weight (rs : List Rows.RowData) (z : ℚ) :
    (rs.map (fun r => { r with weight := z * r.weight })).map Rows.RowData.toRow =
      (rs.map Rows.RowData.toRow).map (Row.scale (z : ℝ)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply, Rows.RowData.toRow, Row.scale, Rat.cast_mul, mul_assoc]

private theorem earlyFour_scaled_gram (suffix : Amplitude)
    (F : Amplitude) (hF : IsAmplitude F) :
    inner (((firstFourRows 4).map Rows.RowData.toRow).map (Row.scale (Rows.inheritedWeight : ℝ)) ++
      suffix) F =
    inner ((stageAmplitude 3).map (Row.scale (Rows.inheritedWeight : ℝ)) ++ suffix) F := by
  have h := stageOne_refine_scaled_inner (additionalEarlyRows 4) suffix F
    (Rows.inheritedWeight : ℝ) hF (by rw [← firstFourRows_split]; exact firstFourRows_validWidths 4)
  dsimp only at h
  rw [← firstFourRows_split, ← initialStageRows_split] at h
  exact h

private theorem stageAmplitude_late (i : Fin 8) (hi : 4 ≤ i.val) :
    stageAmplitude i = (stageAmplitude 3).map (Row.scale (Rows.inheritedWeight : ℝ)) ++
      (Rows.r6 ++ (if 5 ≤ i.val then Rows.r7 else []) ++ (if 6 ≤ i.val then Rows.r8 else []) ++
        (if 7 ≤ i.val then Rows.r9 else [])).map Rows.RowData.toRow := by
  simp only [stageAmplitude, stageRows, if_neg (Nat.not_lt.mpr hi),
    if_pos (show (3 : Fin 8).val < 4 by decide), List.append_assoc, List.map_append, map_weight]
  rfl

private theorem fifthStage_sound (previous : StageBounds)
    (hs : previous.Sound 3) (hc : previous.check 3 = true) :
    (evaluateStage 4 previous).Sound 4 := by
  let z := Rows.inheritedWeight
  let F := (stageAmplitude 3).map (Row.scale (z : ℝ))
  let new := prepareRows Rows.r6
  let inherited := (prepareRows (firstFourRows 4)).map (scaleGridRow · z)
  have hcenter := (centralRows_encloses_inner_G Rows.r6 r6_validWidths).1
  have hvalid (r : GridRow) (hr : r ∈ inherited.toList) : r.Valid := by
    simp only [inherited, Array.toList_map, List.mem_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact (prepareRows_valid (firstFourRows_validWidths 4) hq).scale z
  have hg := gramIncrease_model inherited new hvalid (fun _ hr => prepareRows_valid r6_validWidths hr)
  simp only [inherited, new, modelRows_scale, prepareRows_modelRows] at hg
  have hm := earlyFour_scaled_gram [] _ (rows_isAmplitude r6_validWidths)
  simp only [List.append_nil] at hm
  rw [hm] at hg
  have hbound := fifth_lower_bound previous hs hc F (Rows.r6.map Rows.RowData.toRow)
    z (centralRows new).lower (gramIncrease inherited new) (by norm_num [z, Rows.inheritedWeight])
    (inner_G_scale _ (stageAmplitude_isAmplitude 3) _) (inner_scale_self _ (stageAmplitude_isAmplitude 3) _)
    hcenter hg
  have hF : stageAmplitude 4 = F ++ Rows.r6.map Rows.RowData.toRow := by
    rw [stageAmplitude_late 4 (by decide)]
    rfl
  change _ ≤ certificateQ (stageAmplitude 4)
  rw [hF]
  exact hbound

private theorem lateStep_sound (i j : Fin 8) (hj : 4 ≤ j.val)
    (base : ℚ) (new : List Rows.RowData)
    (hb : (base : ℝ) ≤ certificateQ (stageAmplitude i))
    (hprev : stageAmplitude i =
        (stageAmplitude 3).map (Row.scale (Rows.inheritedWeight : ℝ)) ++
        (Rows.r6 ++ (if 7 ≤ j.val + 1 then Rows.r7 else []) ++
          (if 8 ≤ j.val + 1 then Rows.r8 else [])).map Rows.RowData.toRow)
    (hnext : stageAmplitude j = stageAmplitude i ++ new.map Rows.RowData.toRow)
    (hn : new.all Rows.RowData.validWidths = true) :
    (lateBounds base (j.val + 1) new).Sound j := by
  let stage := j.val + 1
  have hcenter := (centralRows_encloses_inner_G new hn).1
  have hgram := gramIncrease_model (lateInherited stage) (prepareRows new)
    (fun _ hr => lateInherited_valid stage hr) (fun _ hr => prepareRows_valid hn hr)
  rw [modelRows_lateInherited, prepareRows_modelRows,
    earlyFour_scaled_gram _ _ (rows_isAmplitude hn),
    ← hprev] at hgram
  simp only [StageBounds.Sound, if_neg (Nat.not_lt.mpr hj), hnext]
  exact next_lower_bound _ _ base _ _ hb hcenter hgram

theorem evaluateStage_zero_sound (previous : StageBounds) : (evaluateStage 0 previous).Sound 0 :=
  stageOneBounds_sound

theorem evaluateStage_one_sound (b : StageBounds) (hs : b.Sound 0) (hc : b.check 0 = true) :
    (evaluateStage 1 b).Sound 1 :=
  earlyStep_sound 0 1 (by decide) (by decide) b Rows.r3 hs hc (by norm_num [initialStageRows, Fin.val_natCast, List.append_assoc]) r3_validWidths

theorem evaluateStage_two_sound (b : StageBounds) (hs : b.Sound 1) (hc : b.check 1 = true) :
    (evaluateStage 2 b).Sound 2 :=
  earlyStep_sound 1 2 (by decide) (by decide) b Rows.r4 hs hc (by norm_num [initialStageRows, Fin.val_natCast, List.append_assoc]) r4_validWidths

theorem evaluateStage_three_sound (b : StageBounds) (hs : b.Sound 2) (hc : b.check 2 = true) :
    (evaluateStage 3 b).Sound 3 :=
  earlyStep_sound 2 3 (by decide) (by decide) b Rows.r5 hs hc (by norm_num [initialStageRows, Fin.val_natCast, List.append_assoc]) r5_validWidths

theorem evaluateStage_four_sound (b : StageBounds) (hs : b.Sound 3) (hc : b.check 3 = true) :
    (evaluateStage 4 b).Sound 4 :=
  fifthStage_sound b hs hc

theorem evaluateStage_five_sound (b : StageBounds) (hs : b.Sound 4) (hc : b.check 4 = true) :
    (evaluateStage 5 b).Sound 5 :=
  lateStep_sound 4 5 (by decide) (stageProportion 4) Rows.r7
    (late_stage_gain 4 (by decide) b hs hc).le
    (by rw [stageAmplitude_late 4 (by decide)]; norm_num [Fin.val_natCast])
    (by rw [stageAmplitude_late 5 (by decide), stageAmplitude_late 4 (by decide)];
        norm_num [Fin.val_natCast, List.map_append, List.append_assoc])
    r7_validWidths

theorem evaluateStage_six_sound (b : StageBounds) (hs : b.Sound 5) :
    (evaluateStage 6 b).Sound 6 :=
  lateStep_sound 5 6 (by decide) b.lowerProportion Rows.r8 hs
    (by rw [stageAmplitude_late 5 (by decide)]; norm_num [Fin.val_natCast])
    (by rw [stageAmplitude_late 6 (by decide), stageAmplitude_late 5 (by decide)];
        norm_num [Fin.val_natCast, List.map_append, List.append_assoc])
    r8_validWidths

theorem evaluateStage_seven_sound (b : StageBounds) (hs : b.Sound 6) :
    (evaluateStage 7 b).Sound 7 :=
  lateStep_sound 6 7 (by decide) b.lowerProportion Rows.r9 hs
    (by rw [stageAmplitude_late 6 (by decide)]; norm_num [Fin.val_natCast])
    (by rw [stageAmplitude_late 7 (by decide), stageAmplitude_late 6 (by decide)];
        norm_num [Fin.val_natCast, List.map_append, List.append_assoc])
    r9_validWidths

end Chowla.Checker
