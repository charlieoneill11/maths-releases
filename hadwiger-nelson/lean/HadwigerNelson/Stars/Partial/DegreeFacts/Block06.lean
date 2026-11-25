import HadwigerNelson.Stars.Partial.DegreeFacts.Block05

/-! Kernel evaluation of the degree witnesses 49 through 56. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked49 : degreePass 49 = true := by decide +kernel
theorem checked50 : degreePass 50 = true := by decide +kernel
theorem checked51 : degreePass 51 = true := by decide +kernel
theorem checked52 : degreePass 52 = true := by decide +kernel
theorem checked53 : degreePass 53 = true := by decide +kernel
theorem checked54 : degreePass 54 = true := by decide +kernel
theorem checked55 : degreePass 55 = true := by decide +kernel
theorem checked56 : degreePass 56 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
