import Chowla.StageBlocks
import Chowla.StageData

namespace Chowla.Native

open Checker

set_option profiler true in
set_option maxHeartbeats 0 in
theorem stage1_central_checked :
    stageOneCentralCheck stageOneLowerCentral stageOneUpperCentral = true := by
  native_decide

end Chowla.Native
