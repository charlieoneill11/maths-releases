import Chowla.StageCheck
import Chowla.StageData

namespace Chowla.Native

open Checker

set_option profiler true in
set_option maxHeartbeats 0 in
theorem stage2_checked :
    stageCheck 1 reportedStage1 reportedStage2 = true := by
  native_decide

end Chowla.Native
