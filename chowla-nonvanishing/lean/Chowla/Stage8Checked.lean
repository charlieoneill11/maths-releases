import Chowla.Native.Stage8
import Chowla.StageCheck
import Chowla.StageData.Stage7

namespace Chowla.Checker

open Chowla.Native

private theorem stage8Grams_checked :
    List.Forall₂ (fun r v => lateStageGramBlockCheck 7 r v = true)
      (lateBlockRanges 7) stage8Grams := by
  exact .cons stage8_gram_0_6_checked (
    .cons stage8_gram_6_12_checked (
    .cons stage8_gram_12_18_checked (
    .cons stage8_gram_18_26_checked (.nil))))

set_option maxRecDepth 8192 in
theorem stage8Checked :
    stageCheck 7 reportedStage7 reportedStage8 = true := by
  have he := lateStageBounds_eq_report 7 reportedStage7 stage8Center
    stage8Grams (by decide) stage8_central_checked stage8Grams_checked
  have hr : lateStageBoundsFromBlocks 7 reportedStage7 stage8Center
      stage8Grams = reportedStage8 := by decide +kernel
  have hc : reportedStage8.check 7 = true := by decide +kernel
  simp only [stageCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨he.trans hr, hc⟩

end Chowla.Checker
