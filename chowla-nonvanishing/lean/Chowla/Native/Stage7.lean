import Chowla.StagePartition
import Chowla.StageData.Stage7

namespace Chowla.Native

open Checker

set_option profiler true
set_option maxHeartbeats 0

theorem stage7_central_checked :
    lateStageCentralCheck 6 stage7Center = true := by
  native_decide

theorem stage7_gram_0_10_checked :
    lateStageGramBlockCheck 6 (0, 10) stage7Gram1 = true := by
  native_decide

theorem stage7_gram_10_20_checked :
    lateStageGramBlockCheck 6 (10, 20) stage7Gram2 = true := by
  native_decide

theorem stage7_gram_20_35_checked :
    lateStageGramBlockCheck 6 (20, 35) stage7Gram3 = true := by
  native_decide

theorem stage7_gram_35_50_checked :
    lateStageGramBlockCheck 6 (35, 50) stage7Gram4 = true := by
  native_decide

theorem stage7_gram_50_65_checked :
    lateStageGramBlockCheck 6 (50, 65) stage7Gram5 = true := by
  native_decide

theorem stage7_gram_65_80_checked :
    lateStageGramBlockCheck 6 (65, 80) stage7Gram6 = true := by
  native_decide

theorem stage7_gram_80_95_checked :
    lateStageGramBlockCheck 6 (80, 95) stage7Gram7 = true := by
  native_decide

theorem stage7_gram_95_103_checked :
    lateStageGramBlockCheck 6 (95, 103) stage7Gram8 = true := by
  native_decide

end Chowla.Native
