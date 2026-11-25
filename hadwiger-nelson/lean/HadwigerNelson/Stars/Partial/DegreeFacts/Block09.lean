import HadwigerNelson.Stars.Partial.DegreeFacts.Block08

/-! Kernel evaluation of the degree witnesses 73 through 80. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked73 : degreePass 73 = true := by decide +kernel
theorem checked74 : degreePass 74 = true := by decide +kernel
theorem checked75 : degreePass 75 = true := by decide +kernel
theorem checked76 : degreePass 76 = true := by decide +kernel
theorem checked77 : degreePass 77 = true := by decide +kernel
theorem checked78 : degreePass 78 = true := by decide +kernel
theorem checked79 : degreePass 79 = true := by decide +kernel
theorem checked80 : degreePass 80 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
