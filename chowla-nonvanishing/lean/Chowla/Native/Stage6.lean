import Chowla.StagePartition
import Chowla.StageData.Stage6

namespace Chowla.Native

open Checker

set_option profiler true
set_option maxHeartbeats 0

theorem stage6_central_checked :
    lateStageCentralCheck 5 stage6Center = true := by
  native_decide

theorem stage6_gram_0_5_checked :
    lateStageGramBlockCheck 5 (0, 5) stage6Gram1 = true := by
  native_decide

theorem stage6_gram_5_8_checked :
    lateStageGramBlockCheck 5 (5, 8) stage6Gram2 = true := by
  native_decide

theorem stage6_gram_8_10_checked :
    lateStageGramBlockCheck 5 (8, 10) stage6Gram3 = true := by
  native_decide

theorem stage6_gram_10_13_checked :
    lateStageGramBlockCheck 5 (10, 13) stage6Gram4 = true := by
  native_decide

end Chowla.Native
