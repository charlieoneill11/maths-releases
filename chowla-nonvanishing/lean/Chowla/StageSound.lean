import Chowla.CheckerStages

namespace Chowla.Checker

open scoped BigOperators


private theorem central_fold_lower (rs : List GridRow) (center : Option GridSpline)
    (acc : CentralBounds) :
    (rs.foldl (fun b r => addCentralBounds b (centralGrid center r)) acc).lower =
      acc.lower + (rs.map fun r => (centralGrid center r).lower).sum := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons, addCentralBounds]
    ring

private theorem central_fold_upper (rs : List GridRow) (center : Option GridSpline)
    (acc : CentralBounds) :
    (rs.foldl (fun b r => addCentralBounds b (centralGrid center r)) acc).upper =
      acc.upper + (rs.map fun r => (centralGrid center r).upper).sum := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons, addCentralBounds]
    ring

private theorem cast_list_sum (qs : List ℚ) : (qs.sum : ℝ) = (qs.map (↑)).sum :=
  Rat.cast_list_sum _

/-- Sum the rowwise real enclosures using the evaluator's central accumulation. -/
theorem centralRows_sound (rows : List Rows.RowData)
    (hle : ∀ r ∈ rows, ((centralGrid (GridSpline.pack hstarSpline) (prepareGrid r)).lower : ℝ) ≤
      innerGRow r.toRow)
    (hge : ∀ r ∈ rows, innerGRow r.toRow ≤
      ((centralGrid (GridSpline.pack hstarSpline) (prepareGrid r)).upper : ℝ)) :
    let b := centralRows (rows.toArray.map prepareGrid)
    (b.lower : ℝ) ≤ inner_G (rows.map Rows.RowData.toRow) ∧
      inner_G (rows.map Rows.RowData.toRow) ≤ (b.upper : ℝ) := by
  unfold centralRows
  simp only [← Array.foldl_toList, Array.toList_map, central_fold_lower, central_fold_upper,
    zero_add, cast_list_sum, List.map_map, Function.comp_def, inner_G]
  exact ⟨List.sum_le_sum hle, List.sum_le_sum hge⟩

/-- The enclosure step for stages two through four. The previous comparison is
used only to bound its Gram value from above. -/
theorem earlyBounds_sound (i j : Fin 8) (hi : i.val < 4) (hj : j.val < 4)
    (previous : StageBounds) (old new : Array GridRow) (F' : Amplitude)
    (hs : previous.Sound i) (hc : previous.check i = true)
    (hstage : stageAmplitude j = stageAmplitude i ++ F')
    (cl : ((centralRows new).lower : ℝ) ≤ inner_G F')
    (cu : inner_G F' ≤ ((centralRows new).upper : ℝ))
    (gram : (gramIncrease old new : ℝ) = 2 * inner (stageAmplitude i) F' + inner F' F') :
    (earlyBounds i previous old new).Sound j := by
  have hprev := hs
  simp only [StageBounds.Sound, if_pos hi] at hprev
  obtain ⟨hC, hgain⟩ := early_stage_gain i hi previous hs hc
  have hg : 0 < (stageProportion i : ℝ) - (p₀ : ℝ) := by
    fin_cases i <;> norm_num [p₀, stageProportion]
  have hD := chain (stageAmplitude i) F' (previous.upperCentral : ℝ)
    ((stageProportion i : ℝ) - (p₀ : ℝ)) hg hC hprev.2.1 hgain.le
  simp only [StageBounds.Sound, if_pos hj, hstage, earlyBounds, addCentralBounds]
  push_cast
  have hcentral : inner_G (stageAmplitude i ++ F') = inner_G (stageAmplitude i) + inner_G F' := by
    simp [inner_G]
  rw [hcentral, gram]
  exact ⟨add_le_add hprev.1 cl, add_le_add hprev.2.1 cu, hD.trans_eq (by ring)⟩

/-- The first lower bound after scaling the inherited amplitude. This step uses
only the real enclosure of the previous stage and the new central and Gram values. -/
theorem fifth_lower_bound (b : StageBounds) (hs : b.Sound 3) (hc : b.check 3 = true)
    (Fscaled F' : Amplitude) (z c d : ℚ) (hz : 0 ≤ z)
    (hC : inner_G Fscaled = (z : ℝ) * inner_G (stageAmplitude 3))
    (hD : inner Fscaled Fscaled = (z : ℝ)^2 * inner (stageAmplitude 3) (stageAmplitude 3))
    (hcl : (c : ℝ) ≤ inner_G F')
    (hGram : (d : ℝ) = 2 * inner Fscaled F' + inner F' F') :
    ((p₀ + z * b.lowerCentral + c -
        (z^2 * (b.upperCentral^2 / (2 * (stageProportion 3 - p₀))) + d) / 2 : ℚ) : ℝ) ≤
      certificateQ (Fscaled ++ F') := by
  have hprev := hs
  simp only [StageBounds.Sound, if_pos (by decide : (3 : Fin 8).val < 4)] at hprev
  have hCbound := mul_le_mul_of_nonneg_left hprev.1 (show (0 : ℝ) ≤ z by exact_mod_cast hz)
  have hDbound := mul_le_mul_of_nonneg_left (early_gram_bound 3 (by decide) b hs hc).le
    (sq_nonneg (z : ℝ))
  rw [certificateQ_append, certificateQ, hC, hD]
  push_cast
  rw [hGram]
  linarith

/-- The lower-bound recurrence used after stage five. -/
theorem next_lower_bound (F F' : Amplitude) (base c d : ℚ)
    (hb : (base : ℝ) ≤ certificateQ F) (hc : (c : ℝ) ≤ inner_G F')
    (hd : (d : ℝ) = 2 * inner F F' + inner F' F') :
    ((base + c - d / 2 : ℚ) : ℝ) ≤ certificateQ (F ++ F') := by
  rw [certificateQ_append]
  push_cast
  rw [hd]
  linarith

private noncomputable def coeffSum (f : ℕ → ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: as => a * f 0 + coeffSum (fun n => f (n + 1)) as

private theorem coeffSum_eq (f : ℕ → ℝ) (c : List ℝ) :
    (∑ j : Fin c.length, c.get j * f j.val) = coeffSum f c := by
  induction c generalizing f with
  | nil => simp [coeffSum]
  | cons a as ih =>
    calc
      (∑ j : Fin (a :: as).length, (a :: as).get j * f j.val) =
          a * f 0 + ∑ j : Fin as.length, as.get j * f (j.val + 1) :=
        Fin.sum_univ_succ (n := as.length) (fun j => (a :: as).get j * f j.val)
      _ = coeffSum f (a :: as) := by rw [ih (fun n => f (n + 1))]; rfl

private theorem legendreProfile_coeffSum (s : ℝ) (c : List ℝ) (u : ℝ) :
    legendreProfile s c u =
      if u ∈ Set.Icc (-s) s then
        coeffSum (fun j => legendre (2 * (j + 1)) (u / s)) c
      else 0 := by
  classical
  by_cases hu : u ∈ Set.Icc (-s) s
  · simpa only [legendreProfile, Set.indicator_of_mem hu, if_pos hu] using
      coeffSum_eq (fun j => legendre (2 * (j + 1)) (u / s)) c
  · simp [legendreProfile, hu]

/-- The rounding split used in the released stage-one program preserves the
deterministic Fourier profile. The old and additional modes have disjoint degrees. -/
theorem splitStageOneRow_profile (r : Rows.RowData) (hr : r ∈ Rows.r0) :
    (splitStageOneRow r).1.toRow.profile + (splitStageOneRow r).2.toRow.profile =
      r.toRow.profile := by
  simp only [Rows.r0, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  funext u
  by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1 <;>
    simp only [Set.mem_Icc] at hu <;>
    simp [Pi.add_apply, splitStageOneRow, Rows.RowData.toRow, legendreProfile_coeffSum, hu,
      coeffSum, List.replicate_succ];
    ring

end Chowla.Checker
