import HadwigerNelson.Stars.Partial.DegreeFacts.Block04

/-! Kernel evaluation of the degree witnesses 41 through 48. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked41 : degreePass 41 = true := by decide +kernel
theorem checked42 : degreePass 42 = true := by decide +kernel
theorem checked43 : degreePass 43 = true := by decide +kernel
theorem checked44 : degreePass 44 = true := by decide +kernel
theorem checked45 : degreePass 45 = true := by decide +kernel
theorem checked46 : degreePass 46 = true := by decide +kernel
theorem checked47 : degreePass 47 = true := by decide +kernel
theorem checked48 : degreePass 48 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
