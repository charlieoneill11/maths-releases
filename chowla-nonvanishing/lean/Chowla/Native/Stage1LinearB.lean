import Chowla.StageBlocks

namespace Chowla.Native

open Checker

set_option profiler true
set_option maxHeartbeats 0

theorem stage1_linear_360_400_checked :
    stageOneLinearBlockCheck (360, 400) (-3346684102202650390) = true := by
  native_decide

theorem stage1_linear_400_440_checked :
    stageOneLinearBlockCheck (400, 440) (-1819818687443786009) = true := by
  native_decide

theorem stage1_linear_440_480_checked :
    stageOneLinearBlockCheck (440, 480) (-1010636833314564333) = true := by
  native_decide

theorem stage1_linear_480_520_checked :
    stageOneLinearBlockCheck (480, 520) (-252913783377161465) = true := by
  native_decide

theorem stage1_linear_520_560_checked :
    stageOneLinearBlockCheck (520, 560) (-68955007568569558) = true := by
  native_decide

theorem stage1_linear_560_600_checked :
    stageOneLinearBlockCheck (560, 600) 45161107666036231 = true := by
  native_decide

theorem stage1_linear_600_640_checked :
    stageOneLinearBlockCheck (600, 640) (-134722777032138228) = true := by
  native_decide

theorem stage1_linear_640_650_checked :
    stageOneLinearBlockCheck (640, 650) (-70690988999528420) = true := by
  native_decide

end Chowla.Native
