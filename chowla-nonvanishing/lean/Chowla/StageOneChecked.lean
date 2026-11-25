import Chowla.Native.Stage1Central
import Chowla.Native.Stage1LinearA
import Chowla.Native.Stage1LinearB
import Chowla.Native.Stage1Quadratic
import Chowla.StageCheck

namespace Chowla.Checker

open Chowla.Native

private def stageOneLinearReport : List ℤ :=
  [51920838543727407089, 5885976316608900, 1641562857725561083, 2957897063328499273,
   2572815075546037759, -1572337404044362902, -3157283573876751015, -4913034596622494386,
   -3346684102202650390, -1819818687443786009, -1010636833314564333, -252913783377161465,
   -68955007568569558, 45161107666036231, -134722777032138228, -70690988999528420]

private theorem stageOneLinearReport_checked :
    List.Forall₂ (fun r v => stageOneLinearBlockCheck r v = true)
      stageOneLinearRanges stageOneLinearReport := by
  exact .cons stage1_linear_0_80_checked (
    .cons stage1_linear_80_120_checked (
    .cons stage1_linear_120_160_checked (
    .cons stage1_linear_160_200_checked (
    .cons stage1_linear_200_240_checked (
    .cons stage1_linear_240_280_checked (
    .cons stage1_linear_280_320_checked (
    .cons stage1_linear_320_360_checked (
    .cons stage1_linear_360_400_checked (
    .cons stage1_linear_400_440_checked (
    .cons stage1_linear_440_480_checked (
    .cons stage1_linear_480_520_checked (
    .cons stage1_linear_520_560_checked (
    .cons stage1_linear_560_600_checked (
    .cons stage1_linear_600_640_checked (
    .cons stage1_linear_640_650_checked (.nil))))))))))))))))

set_option maxRecDepth 8192 in
private theorem stageOneReport_eq : stageOneBounds () = reportedStage1 := by
  refine (stageOneBounds_eq_report _ _ _ _ stage1_central_checked stageOneLinearReport_checked
    stage1_quadratic_checked).trans ?_
  change stageOneBoundsFromBlocks stageOneLowerCentral stageOneUpperCentral
    stageOneLinearReport 6652304951665526468 = reportedStage1
  decide +kernel

set_option maxRecDepth 8192 in
theorem verifiedStage1 : reportedStage1.Sound 0 ∧ reportedStage1.check 0 = true := by
  refine ⟨stageOneReport_eq ▸ stageOneBounds_sound, ?_⟩
  decide +kernel

end Chowla.Checker
