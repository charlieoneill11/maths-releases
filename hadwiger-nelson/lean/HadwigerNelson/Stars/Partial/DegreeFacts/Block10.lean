import HadwigerNelson.Stars.Partial.DegreeFacts.Block09

/-! Kernel evaluation of the degree witnesses 81 through 88. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked81 : degreePass 81 = true := by decide +kernel
theorem checked82 : degreePass 82 = true := by decide +kernel
theorem checked83 : degreePass 83 = true := by decide +kernel
theorem checked84 : degreePass 84 = true := by decide +kernel
theorem checked85 : degreePass 85 = true := by decide +kernel
theorem checked86 : degreePass 86 = true := by decide +kernel
theorem checked87 : degreePass 87 = true := by decide +kernel
theorem checked88 : degreePass 88 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
