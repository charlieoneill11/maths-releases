import HadwigerNelson.Crossings.ArcIncidence

/-! Conversion of the geometric arc count into the quadratic degree-variance bound. -/
namespace HadwigerNelson.Crossings
open Finset
noncomputable section

theorem degree_variance_of_drawing (X : Finset Plane) (k : ℕ) (hn : 0 < X.card)
    (A : UnitArcDrawing X)
    (half : 4*sampledLower X.card k (unitEdgeCount X) ≤ A.D.crossingCount) :
    (∑ x ∈ X, ((unitDegree X x : ℝ) - 2*(unitEdgeCount X : ℝ)/X.card)^2) ≤
      2*varianceBound X.card k (unitEdgeCount X) := by
  apply variance_from_pairs X k hn
  have upper : (A.D.crossingCount : ℝ) + (∑ x ∈ X, ((unitDegree X x).choose 2 : ℝ)) ≤
      2*(X.card.choose 2 : ℝ) := by exact_mod_cast A.crossing_and_marked
  rw [Nat.cast_choose_two ℝ X.card] at upper
  linarith

end
end HadwigerNelson.Crossings
