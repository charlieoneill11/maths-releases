import HadwigerNelson.Stars.Partial.DegreeFacts.Block03

/-! Kernel evaluation of the degree witnesses 33 through 40. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked33 : degreePass 33 = true := by decide +kernel
theorem checked34 : degreePass 34 = true := by decide +kernel
theorem checked35 : degreePass 35 = true := by decide +kernel
theorem checked36 : degreePass 36 = true := by decide +kernel
theorem checked37 : degreePass 37 = true := by decide +kernel
theorem checked38 : degreePass 38 = true := by decide +kernel
theorem checked39 : degreePass 39 = true := by decide +kernel
theorem checked40 : degreePass 40 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
