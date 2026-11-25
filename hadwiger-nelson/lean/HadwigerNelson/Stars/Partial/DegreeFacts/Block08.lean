import HadwigerNelson.Stars.Partial.DegreeFacts.Block07

/-! Kernel evaluation of the degree witnesses 65 through 72. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked65 : degreePass 65 = true := by decide +kernel
theorem checked66 : degreePass 66 = true := by decide +kernel
theorem checked67 : degreePass 67 = true := by decide +kernel
theorem checked68 : degreePass 68 = true := by decide +kernel
theorem checked69 : degreePass 69 = true := by decide +kernel
theorem checked70 : degreePass 70 = true := by decide +kernel
theorem checked71 : degreePass 71 = true := by decide +kernel
theorem checked72 : degreePass 72 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
