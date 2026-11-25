import HadwigerNelson.Certificate.ScoreIdentity
import HadwigerNelson.Certificate.SearchSound

namespace HadwigerNelson.Certificate
open ParameterBoxes

/-- Every usable box encloses the physical objective with both profile credits.
Products and square roots use directed endpoints, including the mixed
endpoints of the degree variance. -/
theorem point_boxes_sound (b : ParameterBoxes.Box) (m s j : ℕ) (inside : b.Contains m s j)
    (hsj : s+j ≤ 10689) : pointObjective 10689 m s j ≤ (b.upper:ℝ) := by
  rw [← objective_eq _ _ _ hsj]
  exact upper_sound _ _ _ _ inside hsj

/-- The binary partition exhausts the feasible simplex before any leaf
can assert that its rational upper bound is below one. -/
theorem point_bound_of_check (pass : checkBox 55 fullBox = true)
    (m s j : ℕ) (hm : m ≤ 403078) (hsj : s+j ≤ 10689) : pointObjective 10689 m s j < 1 := by
  rw [← objective_eq _ _ _ hsj]
  have h : fullBox.Contains m s j :=
    ⟨⟨Nat.zero_le _,hm⟩,⟨Nat.zero_le _,by change s ≤ 10689; omega⟩,
     ⟨Nat.zero_le _,by change j ≤ 10689; omega⟩⟩
  exact checkBox_sound _ _ _ _ _ h hsj pass

end HadwigerNelson.Certificate
