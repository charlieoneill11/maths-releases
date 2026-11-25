import HadwigerNelson.Certificate.PointBoxes
import HadwigerNelson.Native.Point.Boxes

namespace HadwigerNelson.Certificate

/-- Proposition 53 over all feasible integer triples at the stated order. -/
theorem point_bound_lt_one (m s j : ℕ) (hm : m ≤ 403078) (hsj : s+j ≤ 10689) :
    pointObjective 10689 m s j < 1 :=
  point_bound_of_check ParameterBoxes.boxes_checked m s j hm hsj

end HadwigerNelson.Certificate
