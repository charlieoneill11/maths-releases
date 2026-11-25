import Chowla.StageCheck
import Chowla.StageData
import Chowla.StageData.Stage4

namespace Chowla.Native

open Checker

set_option profiler true in
set_option maxHeartbeats 0 in
theorem stage4_checked :
    stageCheck 3 reportedStage3 reportedStage4 = true := by
  native_decide

end Chowla.Native
