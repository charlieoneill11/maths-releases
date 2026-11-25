import Chowla.Native.Stage6
import Chowla.StageCheck
import Chowla.StageData.Stage5

namespace Chowla.Checker

open Chowla.Native

private theorem stage6Grams_checked :
    List.Forall₂ (fun r v => lateStageGramBlockCheck 5 r v = true)
      (lateBlockRanges 5) stage6Grams := by
  exact .cons stage6_gram_0_5_checked (
    .cons stage6_gram_5_8_checked (
    .cons stage6_gram_8_10_checked (
    .cons stage6_gram_10_13_checked (.nil))))

set_option maxRecDepth 8192 in
theorem stage6Checked :
    stageCheck 5 reportedStage5 reportedStage6 = true := by
  have he := lateStageBounds_eq_report 5 reportedStage5 stage6Center
    stage6Grams (by decide) stage6_central_checked stage6Grams_checked
  have hr : lateStageBoundsFromBlocks 5 reportedStage5 stage6Center
      stage6Grams = reportedStage6 := by decide +kernel
  have hc : reportedStage6.check 5 = true := by decide +kernel
  simp only [stageCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨he.trans hr, hc⟩

end Chowla.Checker
