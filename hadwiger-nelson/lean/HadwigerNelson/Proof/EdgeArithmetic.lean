import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace HadwigerNelson.Proof

/-- The final strict integer inequality in the paper's quadrature-based §4 proof. -/
theorem printed_edge_margin : 245510 * 2036573446989 < 5 * 10^17 := by decide

/-- A probability enclosure from Proposition 12 can be used directly in both
applications. The star bound recovers 4·10⁻⁹ per edge. -/
theorem edge_margins_of_strict {p : ℝ}
    (hp : p < 1 / 245510 + 4 / 10^9) :
    245269 * p < 1 ∧ 245510 * (p - (8 / 10^9) / 2) < 1 := by
  constructor <;> linarith

/-- Transfer a strict bound for the maximum edge count to a graph below the cap.
This also covers a nonpositive coefficient. -/
theorem mul_lt_one_of_card_le {m K : ℕ} {a : ℝ} (hm : m ≤ K) (hK : (K : ℝ) * a < 1) :
    (m : ℝ) * a < 1 := by
  rcases le_total 0 a with ha | ha
  · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) ha).trans_lt hK
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ha).trans_lt zero_lt_one

end HadwigerNelson.Proof
