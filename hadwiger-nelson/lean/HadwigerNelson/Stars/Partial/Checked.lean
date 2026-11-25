import Mathlib.Tactic.FinCases
import HadwigerNelson.Stars.Partial.Certified
import HadwigerNelson.Stars.Partial.DegreeFacts
import HadwigerNelson.Native.PartialLayout.SourceBoxes
import HadwigerNelson.Native.PartialStars.Shard0
import HadwigerNelson.Native.PartialStars.Shard1
import HadwigerNelson.Native.PartialStars.Shard2
import HadwigerNelson.Native.PartialStars.Shard3

namespace HadwigerNelson.Stars.PartialCheck

/-- The fixed W_V gives at least 901 picounits of gain per incidence for
every positive degree and every configuration of incident directions. -/
theorem cellScore_lower {d : Nat} (hd : 0 < d) (φ : Fin d → ℝ) :
    (901 : ℝ)/10^12 ≤ cellScore PartialWave.datum φ := by
  apply beta_cell_of_checks (Layout.check_physical Layout.checked) _ data_checked hd φ
  intro p
  fin_cases p
  · exact Native.shard0
  · exact Native.shard1
  · exact Native.shard2
  · exact Native.shard3

end HadwigerNelson.Stars.PartialCheck
