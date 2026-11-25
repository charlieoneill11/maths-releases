import Chowla.Native.Stage7
import Chowla.StageCheck
import Chowla.StageData.Stage6

namespace Chowla.Checker

open Chowla.Native

private theorem stage7Grams_checked :
    List.Forall₂ (fun r v => lateStageGramBlockCheck 6 r v = true)
      (lateBlockRanges 6) stage7Grams := by
  exact .cons stage7_gram_0_10_checked (
    .cons stage7_gram_10_20_checked (
    .cons stage7_gram_20_35_checked (
    .cons stage7_gram_35_50_checked (
    .cons stage7_gram_50_65_checked (
    .cons stage7_gram_65_80_checked (
    .cons stage7_gram_80_95_checked (
    .cons stage7_gram_95_103_checked (.nil))))))))

set_option maxRecDepth 8192 in
theorem stage7Checked :
    stageCheck 6 reportedStage6 reportedStage7 = true := by
  have he := lateStageBounds_eq_report 6 reportedStage6 stage7Center
    stage7Grams (by decide) stage7_central_checked stage7Grams_checked
  have hr : lateStageBoundsFromBlocks 6 reportedStage6 stage7Center
      stage7Grams = reportedStage7 := by decide +kernel
  have hc : reportedStage7.check 6 = true := by decide +kernel
  simp only [stageCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨he.trans hr, hc⟩

end Chowla.Checker
