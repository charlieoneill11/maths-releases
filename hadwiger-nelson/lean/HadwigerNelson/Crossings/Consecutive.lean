import HadwigerNelson.Plane

namespace HadwigerNelson.Centres

/-- A chord separates the two open arcs of its circle. Its endpoints are
consecutive marked points exactly when all marked points lie on one closed side. -/
def side (p q r : Plane) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

def consecutive (X : Finset Plane) (u p q : Plane) : Prop :=
  p ≠ q ∧ dist u p = 1 ∧ dist u q = 1 ∧
    ((∀ r ∈ X, dist u r = 1 → 0 ≤ side p q r) ∨ (∀ r ∈ X, dist u r = 1 → side p q r ≤ 0))

end HadwigerNelson.Centres
