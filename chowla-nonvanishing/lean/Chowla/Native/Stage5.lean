import Chowla.StageCheck
import Chowla.StageData.Stage4
import Chowla.StageData.Stage5

namespace Chowla.Native

open Checker

set_option profiler true in
set_option maxHeartbeats 0 in
theorem stage5_checked :
    stageCheck 4 reportedStage4 reportedStage5 = true := by
  native_decide

end Chowla.Native
