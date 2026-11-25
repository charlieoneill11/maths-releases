import Chowla.Model.Scaling
import Chowla.StageSound

namespace Chowla

open MeasureTheory

/-- The central product is additive when a row is split into profiles with a common pattern. -/
theorem innerGRow_add_profile (k k₁ k₂ : Row) (hk : k.Admissible)
    (hk₁ : k₁.Admissible) (hk₂ : k₂.Admissible)
    (h₁ : k₁.widths = k.widths) (h₂ : k₂.widths = k.widths)
    (h : k.profile = k₁.profile + k₂.profile) :
    innerGRow k = innerGRow k₁ + innerGRow k₂ := by
  by_cases he : k.widths = []
  · rw [innerGRow_nil _ hk he, innerGRow_nil _ hk₁ (h₁.trans he),
      innerGRow_nil _ hk₂ (h₂.trans he), add_zero]
  · rw [innerGRow_eq_cumulant _ hk he, innerGRow_eq_cumulant _ hk₁ (fun hn => he (h₁.symm.trans hn)),
      innerGRow_eq_cumulant _ hk₂ (fun hn => he (h₂.symm.trans hn)), h₁, h₂, h,
      convolve_comm H, convolve_add_head hk₁.2.1 hk₂.2.1 (integrable_of_isProfile H_isProfile)]
    have hprofiles : ∀ f ∈ k.widths.map rectangle, IsProfile f := by
      intro f hf
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
      exact rectangle_isProfile a
    rw [cumulant_add_head (convolve_isProfile hk₁.2.1 H_isProfile)
      (convolve_isProfile hk₂.2.1 H_isProfile) _ hprofiles]
    rw [convolve_comm k₁.profile H, convolve_comm k₂.profile H]

namespace Checker

private theorem stageOne_r0_valid (r : Rows.RowData) (hr : r ∈ Rows.r0) :
    r.validWidths = true := by
  simp only [Rows.r0, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  decide

private theorem r0_admissible (r : Rows.RowData) (hr : r ∈ Rows.r0) :
    r.toRow.Admissible ∧ (splitStageOneRow r).1.toRow.Admissible ∧
      (splitStageOneRow r).2.toRow.Admissible := by
  have h := stageOne_r0_valid r hr
  refine ⟨r.toRow_admissible_of_widths (r.validWidths_sound h).1 (r.validWidths_sound h).2, ?_⟩
  let r₁ := (splitStageOneRow r).1
  let r₂ := (splitStageOneRow r).2
  have h₁ : r₁.validWidths = true := h
  have h₂ : r₂.validWidths = true := h
  exact ⟨r₁.toRow_admissible_of_widths (r₁.validWidths_sound h₁).1 (r₁.validWidths_sound h₁).2,
    r₂.toRow_admissible_of_widths (r₂.validWidths_sound h₂).1 (r₂.validWidths_sound h₂).2⟩

/-- The representation split for stage-one rounding preserves any additive row evaluation. -/
private theorem sum_stageOne_coalesced (f : Row → ℝ) (extras : List Rows.RowData)
    (hf : ∀ r ∈ Rows.r0,
      f (splitStageOneRow r).1.toRow + f (splitStageOneRow r).2.toRow = f r.toRow) :
    (((stageOneLinear ++ stageOneQuadratic ++ extras).map Rows.RowData.toRow).map f).sum =
      ((((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ extras).map
        Rows.RowData.toRow).map f).sum := by
  simp only [stageOneLinear, stageOneQuadratic, List.map_append, List.sum_append, List.map_map]
  have hs₀ :
      (Rows.r0.map (f ∘ Rows.RowData.toRow)).sum =
        (Rows.r0.map ((f ∘ Rows.RowData.toRow) ∘ fun r => (splitStageOneRow r).1)).sum +
        (Rows.r0.map ((f ∘ Rows.RowData.toRow) ∘ fun r => (splitStageOneRow r).2)).sum := by
    rw [← List.sum_map_add]
    apply congrArg List.sum
    exact List.map_congr_left (fun r hr => (hf r hr).symm)
  rw [hs₀]
  simp only [Function.comp_def]
  abel

/-- The split and coalesced representations have the same width checks. -/
theorem stageOne_refine_validWidths (extras : List Rows.RowData) :
    (stageOneLinear ++ stageOneQuadratic ++ extras).all Rows.RowData.validWidths = true ↔
      ((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ extras).all
        Rows.RowData.validWidths = true := by
  simp only [stageOneLinear, stageOneQuadratic, List.all_append, List.all_map, Bool.and_eq_true,
    Function.comp_def, splitStageOneRow, Rows.RowData.validWidths]
  tauto

private theorem amplitude_of_widthChecks (rows : List Rows.RowData)
    (h : rows.all Rows.RowData.validWidths = true) : IsAmplitude (rows.map Rows.RowData.toRow) := by
  intro k hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
  obtain ⟨hw, hs⟩ := r.validWidths_sound (List.all_eq_true.mp h r hr)
  exact r.toRow_admissible_of_widths hw hs

/-- Coalescing the deterministic split preserves the mixed Gram product with any
admissible amplitude, including after common rows have been appended. -/
theorem stageOne_refine_inner (extras : List Rows.RowData) (F : Amplitude) (hF : IsAmplitude F) :
    inner ((stageOneLinear ++ stageOneQuadratic ++ extras).map Rows.RowData.toRow) F =
      inner (((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ extras).map
        Rows.RowData.toRow) F := by
  unfold inner
  apply sum_stageOne_coalesced
  intro r hr
  obtain ⟨hk, hk₁, hk₂⟩ := r0_admissible r hr
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  exact (innerRow_add_profile _ _ _ _ hk hk₁ hk₂ (hF l hl) rfl rfl
    (splitStageOneRow_profile r hr).symm).symm

/-- Coalescing the deterministic split preserves the central product after
any common rows have been appended. -/
theorem stageOne_refine_inner_G (extras : List Rows.RowData) :
    inner_G ((stageOneLinear ++ stageOneQuadratic ++ extras).map Rows.RowData.toRow) =
      inner_G (((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ extras).map
        Rows.RowData.toRow) := by
  unfold inner_G
  apply sum_stageOne_coalesced
  intro r hr
  obtain ⟨hk, hk₁, hk₂⟩ := r0_admissible r hr
  exact (innerGRow_add_profile _ _ _ hk hk₁ hk₂ rfl rfl
    (splitStageOneRow_profile r hr).symm).symm

/-- For admissible appended rows, the split and coalesced Gram squares agree. -/
theorem stageOne_refine_gram (extras : List Rows.RowData)
    (hvalid : (stageOneLinear ++ stageOneQuadratic ++ extras).all Rows.RowData.validWidths = true) :
    let split := (stageOneLinear ++ stageOneQuadratic ++ extras).map Rows.RowData.toRow
    let combined := ((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ extras).map
      Rows.RowData.toRow
    inner split split = inner combined combined := by
  dsimp only
  have hsplit := amplitude_of_widthChecks _ hvalid
  have hcombined := amplitude_of_widthChecks _ ((stageOne_refine_validWidths extras).mp hvalid)
  exact (stageOne_refine_inner extras _ hsplit).trans
    ((inner_comm _ _).trans (stageOne_refine_inner extras _ hcombined))

/-- Coalescing also preserves mixed Gram products when the inherited rows are
uniformly scaled and followed by a common suffix. -/
theorem stageOne_refine_scaled_inner (inherited : List Rows.RowData) (suffix F : Amplitude)
    (z : ℝ) (hF : IsAmplitude F)
    (hvalid : (stageOneLinear ++ stageOneQuadratic ++ inherited).all Rows.RowData.validWidths = true) :
    let split := (stageOneLinear ++ stageOneQuadratic ++ inherited).map Rows.RowData.toRow
    let combined := ((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ inherited).map
      Rows.RowData.toRow
    inner (split.map (Row.scale z) ++ suffix) F = inner (combined.map (Row.scale z) ++ suffix) F := by
  dsimp only
  have hsplit := amplitude_of_widthChecks _ hvalid
  have hcombined := amplitude_of_widthChecks _ ((stageOne_refine_validWidths inherited).mp hvalid)
  rw [inner_append_left, inner_append_left, inner_scale_left _ _ hsplit hF,
    inner_scale_left _ _ hcombined hF, stageOne_refine_inner inherited F hF]

/-- The central product agrees after scaling the inherited rows and appending
any common suffix. -/
theorem stageOne_refine_scaled_inner_G (inherited : List Rows.RowData) (suffix : Amplitude)
    (z : ℝ)
    (hvalid : (stageOneLinear ++ stageOneQuadratic ++ inherited).all Rows.RowData.validWidths = true) :
    let split := (stageOneLinear ++ stageOneQuadratic ++ inherited).map Rows.RowData.toRow
    let combined := ((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ inherited).map
      Rows.RowData.toRow
    inner_G (split.map (Row.scale z) ++ suffix) = inner_G (combined.map (Row.scale z) ++ suffix) := by
  dsimp only
  have hsplit := amplitude_of_widthChecks _ hvalid
  have hcombined := amplitude_of_widthChecks _ ((stageOne_refine_validWidths inherited).mp hvalid)
  have hadd (A B : Amplitude) : inner_G (A ++ B) = inner_G A + inner_G B := by
    simp only [inner_G, List.map_append, List.sum_append]
  rw [hadd, hadd, inner_G_scale _ hsplit, inner_G_scale _ hcombined, stageOne_refine_inner_G]

private theorem inner_append_self (A B : Amplitude) :
    inner (A ++ B) (A ++ B) = inner A A + 2 * inner A B + inner B B := by
  rw [inner_append_left, inner_append_right, inner_append_right, inner_comm B A]
  ring

/-- The Gram square agrees after scaling the inherited rows and appending any
common admissible suffix. -/
theorem stageOne_refine_scaled_gram (inherited : List Rows.RowData) (suffix : Amplitude) (z : ℝ)
    (hsuffix : IsAmplitude suffix)
    (hvalid : (stageOneLinear ++ stageOneQuadratic ++ inherited).all Rows.RowData.validWidths = true) :
    let split := ((stageOneLinear ++ stageOneQuadratic ++ inherited).map
      Rows.RowData.toRow).map (Row.scale z) ++ suffix
    let combined := (((Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2) ++ inherited).map
      Rows.RowData.toRow).map (Row.scale z) ++ suffix
    inner split split = inner combined combined := by
  dsimp only
  have hsplit := amplitude_of_widthChecks _ hvalid
  have hcombined := amplitude_of_widthChecks _ ((stageOne_refine_validWidths inherited).mp hvalid)
  rw [inner_append_self, inner_append_self, inner_scale_self _ hsplit, inner_scale_self _ hcombined,
    inner_scale_left _ _ hsplit hsuffix, inner_scale_left _ _ hcombined hsuffix,
    stageOne_refine_gram inherited hvalid, stageOne_refine_inner inherited suffix hsuffix]

end Checker
end Chowla
