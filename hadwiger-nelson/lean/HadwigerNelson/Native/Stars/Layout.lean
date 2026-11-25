import HadwigerNelson.Stars.LayoutSound

namespace HadwigerNelson.Stars.BoxCheck

/-- The 14,464 harmonic boxes and 252 saturated boxes satisfy the containment
and separation checks interpreted by `checkSourceBoxes_physical`. -/
theorem sourceBoxes_checked : checkSourceBoxes = true := by native_decide

theorem complete_layout : PhysicalLayout := checkSourceBoxes_physical sourceBoxes_checked

end HadwigerNelson.Stars.BoxCheck
