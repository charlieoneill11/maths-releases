import HadwigerNelson.Stars.Partial.DegreeFacts.Block02

/-! Kernel evaluation of the degree witnesses 25 through 32. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked25 : degreePass 25 = true := by decide +kernel
theorem checked26 : degreePass 26 = true := by decide +kernel
theorem checked27 : degreePass 27 = true := by decide +kernel
theorem checked28 : degreePass 28 = true := by decide +kernel
theorem checked29 : degreePass 29 = true := by decide +kernel
theorem checked30 : degreePass 30 = true := by decide +kernel
theorem checked31 : degreePass 31 = true := by decide +kernel
theorem checked32 : degreePass 32 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
