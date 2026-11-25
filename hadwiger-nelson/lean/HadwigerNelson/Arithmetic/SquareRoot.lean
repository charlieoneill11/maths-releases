import HadwigerNelson.Arithmetic.Rounding
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Sqrt

/-! Directed square-root and harmonic magnitude bounds for the moment checkers. -/

namespace HadwigerNelson.Arithmetic

/-- Both one-tick bounds for the integer square root of a nonnegative signed input. -/
theorem sqrtInt_spec (z : Int) (hz : 0 ≤ z) :
    (Int.sqrt z : ℝ) ≤ Real.sqrt (z:ℝ) ∧ Real.sqrt (z:ℝ) < (Int.sqrt z : ℝ)+1 := by
  lift z to Nat using hz
  simp only [Int.sqrt_natCast, Int.cast_natCast]
  exact ⟨Real.nat_sqrt_le_real_sqrt, Real.real_sqrt_lt_nat_sqrt_succ⟩

/-- C++ magnitude truncates the integer square root before dividing by harmonic k. -/
theorem magnitude_floor (x y k : Int) (hk : 0 < k) :
    ((Int.sqrt (x*x+y*y) / k : Int) : ℝ) ≤ Real.sqrt ((x:ℝ)^2 + (y:ℝ)^2) / k := by
  apply (floorDiv_le_real _ hk).trans
  apply (div_le_div_iff_of_pos_right (show (0:ℝ)<k by exact_mod_cast hk)).2
  have hz : 0 ≤ x*x+y*y := by nlinarith [sq_nonneg x,sq_nonneg y]
  simpa [sq] using (sqrtInt_spec _ hz).1

end HadwigerNelson.Arithmetic
