import HadwigerNelson.Certificate.SearchSound

namespace HadwigerNelson.Certificate.ParameterBoxes

/-- Both centre profiles and both forest modes give an upper bound below one
on every feasible integer triple in the full finite search. -/
theorem boxes_checked : checkBox 55 fullBox = true := by native_decide

end HadwigerNelson.Certificate.ParameterBoxes
