import Chowla.StageCheck
import Chowla.StageData

namespace Chowla.Native

open Checker

set_option profiler true in
set_option maxHeartbeats 0 in
theorem stage3_checked :
    stageCheck 2 reportedStage2 reportedStage3 = true := by
  native_decide

end Chowla.Native
