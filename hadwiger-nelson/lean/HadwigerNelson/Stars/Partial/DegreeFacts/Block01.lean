import HadwigerNelson.Stars.Partial.DegreeFacts.Block00

/-! Kernel evaluation of the degree witnesses 9 through 16. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked09 : degreePass 9 = true := by decide +kernel
theorem checked10 : degreePass 10 = true := by decide +kernel
theorem checked11 : degreePass 11 = true := by decide +kernel
theorem checked12 : degreePass 12 = true := by decide +kernel
theorem checked13 : degreePass 13 = true := by decide +kernel
theorem checked14 : degreePass 14 = true := by decide +kernel
theorem checked15 : degreePass 15 = true := by decide +kernel
theorem checked16 : degreePass 16 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
