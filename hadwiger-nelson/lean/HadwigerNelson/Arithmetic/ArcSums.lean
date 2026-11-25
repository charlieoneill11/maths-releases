import HadwigerNelson.Arithmetic.Rounding

/-! Signed sums over consecutive angular bins. Both endpoints of a span use the same prefix. -/

namespace HadwigerNelson.Arithmetic

/-- Bounds on every angular increment imply bounds on every contiguous span.
Using lower-prefix differences here preserves the sum of the directed errors. -/
theorem arc_prefix_bounds (low high : Nat → Int) (angle : Nat → ℝ) {i j : Nat}
    (hij : i ≤ j) (hstep : ∀ k, i ≤ k → k < j →
      ((low (k+1)-low k : Int) : ℝ) ≤ angle (k+1)-angle k ∧
      angle (k+1)-angle k ≤ ((high (k+1)-high k : Int) : ℝ)) :
    ((low j-low i : Int) : ℝ) ≤ angle j-angle i ∧
      angle j-angle i ≤ ((high j-high i : Int) : ℝ) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    obtain ⟨lp,hp⟩ := ih (fun k hk hkj => hstep k hk (by omega))
    obtain ⟨ls,hs⟩ := hstep j hij (by omega)
    push_cast at *
    constructor <;> linarith

/-- A signed arc picks its upper length for a negative coefficient in a lower sum. -/
theorem signed_arc_lower (c low high : Int) (angle : ℝ) (hl : (low:ℝ) ≤ angle)
    (hh : angle ≤ (high:ℝ)) :
    ((c*(if c < 0 then high else low) : Int) : ℝ) ≤ (c:ℝ)*angle := by
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonpos_left hh (by exact_mod_cast hc.le)
  · push_cast
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast (le_of_not_gt hc))

end HadwigerNelson.Arithmetic
