import HadwigerNelson.Angular.Grid
import HadwigerNelson.Angular.Constants

namespace HadwigerNelson.CompleteWave
open HadwigerNelson.Angular.Grid

/-- A representative of the complete right boundary on the fundamental height interval. -/
noncomputable def rightAt (y : ℝ) : ℝ :=
  interpolation (fun i => (ordinate i : ℝ)/scale) 2048 (4096*y)

theorem rightAt_continuous : Continuous rightAt :=
  (interpolation_continuous _ _).comp (continuous_const.mul continuous_id)

end HadwigerNelson.CompleteWave
