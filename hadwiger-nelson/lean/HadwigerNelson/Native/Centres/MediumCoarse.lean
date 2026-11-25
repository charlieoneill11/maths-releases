import HadwigerNelson.Centres.Events.Medium

namespace HadwigerNelson.Centres.Quadrature.Native

/-- Coarse-profile overlap integrals on all 61 medium chord intervals.
The real displacement bound is `mediumPass_real`. -/
theorem mediumCoarse : mediumCheck false = true := by native_decide

end HadwigerNelson.Centres.Quadrature.Native
