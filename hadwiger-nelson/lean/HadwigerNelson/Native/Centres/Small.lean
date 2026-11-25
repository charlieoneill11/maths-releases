import HadwigerNelson.Centres.Events.Small

namespace HadwigerNelson.Centres.Quadrature.Native

/-- All six small-chord rectangle quadratures. Their actual physical widths
are bounded by `smallPass_real`. -/
theorem smallIntervals : smallCheck = true := by native_decide

end HadwigerNelson.Centres.Quadrature.Native
