import HadwigerNelson.Stars.Partial.DegreeFacts.Block01

/-! Kernel evaluation of the degree witnesses 17 through 24. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked17 : degreePass 17 = true := by decide +kernel
theorem checked18 : degreePass 18 = true := by decide +kernel
theorem checked19 : degreePass 19 = true := by decide +kernel
theorem checked20 : degreePass 20 = true := by decide +kernel
theorem checked21 : degreePass 21 = true := by decide +kernel
theorem checked22 : degreePass 22 = true := by decide +kernel
theorem checked23 : degreePass 23 = true := by decide +kernel
theorem checked24 : degreePass 24 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
