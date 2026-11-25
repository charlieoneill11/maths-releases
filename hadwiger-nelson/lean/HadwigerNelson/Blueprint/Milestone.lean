import HadwigerNelson.Angular.Checked
import HadwigerNelson.Angular.Probability
import HadwigerNelson.Proof.UnionEdges
import HadwigerNelson.Proof.EdgeArithmetic
import HadwigerNelson.Placement.CompleteBlank

namespace HadwigerNelson
open MeasureTheory
noncomputable section

namespace Wave

/-- The consequence of Theorem 3 obtained from the certified integer bins of
Proposition 12, with no assertion about the separate midpoint quadrature. -/
theorem complete_monoProb_upper :
    Placement.meanMonoProb completeDatum ≤ (Angular.completeUpper : ℝ) :=
  Angular.complete_probability_of_sum Angular.complete_integer_bound

end Wave

/-- The 245,269-edge milestone uses only the one-edge probability estimate. -/
theorem edges_le_245269 (E : Finset (Plane × Plane)) (hE : ∀ e ∈ E, dist e.1 e.2 = 1)
    (hcard : E.card ≤ 245269) : ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 := by
  apply Proof.edges_of_union_bound Wave.completeDatum (Angular.completeUpper : ℝ) E
    hE Wave.complete_ae_nonblank Wave.complete_monoProb_upper
  apply Proof.mul_lt_one_of_card_le hcard
  exact_mod_cast Angular.completeUpper_milestone

end
end HadwigerNelson
