import Chowla.StageBlocks

namespace Chowla.Native

open Checker

set_option profiler true
set_option maxHeartbeats 0

theorem stage1_quadratic_checked :
    stageOneQuadraticBlockCheck 6652304951665526468 = true := by
  native_decide

end Chowla.Native
