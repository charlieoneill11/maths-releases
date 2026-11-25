import Chowla.StagePartition
import Chowla.StageData.Stage8

namespace Chowla.Native

open Checker

set_option profiler true
set_option maxHeartbeats 0

theorem stage8_central_checked :
    lateStageCentralCheck 7 stage8Center = true := by
  native_decide

theorem stage8_gram_0_6_checked :
    lateStageGramBlockCheck 7 (0, 6) stage8Gram1 = true := by
  native_decide

theorem stage8_gram_6_12_checked :
    lateStageGramBlockCheck 7 (6, 12) stage8Gram2 = true := by
  native_decide

theorem stage8_gram_12_18_checked :
    lateStageGramBlockCheck 7 (12, 18) stage8Gram3 = true := by
  native_decide

theorem stage8_gram_18_26_checked :
    lateStageGramBlockCheck 7 (18, 26) stage8Gram4 = true := by
  native_decide

end Chowla.Native
