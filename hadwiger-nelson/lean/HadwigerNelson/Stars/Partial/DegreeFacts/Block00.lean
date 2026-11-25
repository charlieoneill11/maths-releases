import HadwigerNelson.Stars.Partial.CertificateRuntime

/-! Kernel evaluation of the degree witnesses 1 through 8. -/
namespace HadwigerNelson.Stars.PartialCheck.DegreeFacts
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem checked01 : degreePass 1 = true := by decide +kernel
theorem checked02 : degreePass 2 = true := by decide +kernel
theorem checked03 : degreePass 3 = true := by decide +kernel
theorem checked04 : degreePass 4 = true := by decide +kernel
theorem checked05 : degreePass 5 = true := by decide +kernel
theorem checked06 : degreePass 6 = true := by decide +kernel
theorem checked07 : degreePass 7 = true := by decide +kernel
theorem checked08 : degreePass 8 = true := by decide +kernel

end HadwigerNelson.Stars.PartialCheck.DegreeFacts
