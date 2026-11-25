import HadwigerNelson.Stars.Partial.Layout

namespace HadwigerNelson.Stars.PartialCheck.Layout

/-- The four source families have the real geometry certified by `check_physical`. -/
theorem checked : check = true := by native_decide

end HadwigerNelson.Stars.PartialCheck.Layout
