import HadwigerNelson.Stars.Partial.DegreeFacts.Block06

/-! Kernel evaluation of the degree witnesses 57 through 64. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked57 : degreePass 57 = true := by decide +kernel
theorem checked58 : degreePass 58 = true := by decide +kernel
theorem checked59 : degreePass 59 = true := by decide +kernel
theorem checked60 : degreePass 60 = true := by decide +kernel
theorem checked61 : degreePass 61 = true := by decide +kernel
theorem checked62 : degreePass 62 = true := by decide +kernel
theorem checked63 : degreePass 63 = true := by decide +kernel
theorem checked64 : degreePass 64 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
