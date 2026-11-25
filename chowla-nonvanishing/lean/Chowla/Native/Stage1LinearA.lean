import Chowla.StageBlocks

namespace Chowla.Native

open Checker

set_option profiler true
set_option maxHeartbeats 0

theorem stage1_linear_0_80_checked :
    stageOneLinearBlockCheck (0, 80) 51920838543727407089 = true := by
  native_decide

theorem stage1_linear_80_120_checked :
    stageOneLinearBlockCheck (80, 120) 5885976316608900 = true := by
  native_decide

theorem stage1_linear_120_160_checked :
    stageOneLinearBlockCheck (120, 160) 1641562857725561083 = true := by
  native_decide

theorem stage1_linear_160_200_checked :
    stageOneLinearBlockCheck (160, 200) 2957897063328499273 = true := by
  native_decide

theorem stage1_linear_200_240_checked :
    stageOneLinearBlockCheck (200, 240) 2572815075546037759 = true := by
  native_decide

theorem stage1_linear_240_280_checked :
    stageOneLinearBlockCheck (240, 280) (-1572337404044362902) = true := by
  native_decide

theorem stage1_linear_280_320_checked :
    stageOneLinearBlockCheck (280, 320) (-3157283573876751015) = true := by
  native_decide

theorem stage1_linear_320_360_checked :
    stageOneLinearBlockCheck (320, 360) (-4913034596622494386) = true := by
  native_decide

end Chowla.Native
