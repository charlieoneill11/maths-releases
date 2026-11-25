import Legendre.Arithmetic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Legendre.Arithmetic

private def bisect (target lo hi : ℕ) : ℕ :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if mid ^ 10 ≤ target then bisect target mid hi else bisect target lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

private theorem bisect_sound (target lo hi : ℕ)
    (hlo : lo ^ 10 ≤ target) (hhi : target < hi ^ 10) :
    bisect target lo hi ^ 10 ≤ target ∧ target < (bisect target lo hi + 1) ^ 10 := by
  rw [bisect]
  split
  · dsimp only
    split
    · exact bisect_sound target ((lo + hi) / 2) hi (by assumption) hhi
    · exact bisect_sound target lo ((lo + hi) / 2) hlo (Nat.lt_of_not_ge (by assumption))
  · rename_i h
    have hlast : hi ≤ lo + 1 := Nat.le_of_not_gt h
    exact ⟨hlo, hhi.trans_le (Nat.pow_le_pow_left hlast 10)⟩
termination_by hi - lo
decreasing_by all_goals omega

def rootScale : ℕ := 2 ^ 200

private theorem rootScale_pos : 0 < rootScale := by unfold rootScale; positivity

private def rootNumerator (n : ℕ) : ℕ :=
  bisect (n * rootScale ^ 10) 0 ((n + 1) * rootScale)

/-- The scaled integer bounds that certify a tenth root. -/
theorem rootNumerator_sound (n : ℕ) :
    rootNumerator n ^ 10 ≤ n * rootScale ^ 10 ∧
      n * rootScale ^ 10 < (rootNumerator n + 1) ^ 10 := by
  refine bisect_sound _ _ _ (by simp) ?_
  rw [mul_pow]
  apply Nat.mul_lt_mul_of_pos_right _ (pow_pos rootScale_pos 10)
  exact (Nat.lt_succ_self n).trans_le (le_self_pow₀ (by omega) (by decide : 10 ≠ 0))

/-- Enclose the tenth root by adjacent multiples of `2⁻²⁰⁰`. -/
def tenthRoot (n : ℕ) : Bounds :=
  ⟨(rootNumerator n : ℚ) / rootScale, ((rootNumerator n + 1 : ℕ) : ℚ) / rootScale⟩

theorem tenthRoot_sound (n : ℕ) : (tenthRoot n).Encloses ((n : ℝ) ^ (1 / 10 : ℝ)) := by
  have hs : 0 < (rootScale : ℝ) := by exact_mod_cast rootScale_pos
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hpow : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = (n : ℝ) := by
    rw [← Real.rpow_mul_natCast hn]
    norm_num
  have hlo : ((rootNumerator n : ℝ) / rootScale) ^ (10 : ℕ) ≤ (n : ℝ) := by
    rw [div_pow, div_le_iff₀ (pow_pos hs 10)]
    exact_mod_cast (rootNumerator_sound n).1
  have hhi : (n : ℝ) < (((rootNumerator n + 1 : ℕ) : ℝ) / rootScale) ^ (10 : ℕ) := by
    rw [div_pow, lt_div_iff₀ (pow_pos hs 10)]
    exact_mod_cast (rootNumerator_sound n).2
  rw [← hpow] at hlo hhi
  have hl := (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hn _) (by decide)).1 hlo
  have hu := (pow_lt_pow_iff_left₀ (Real.rpow_nonneg hn _) (by positivity) (by decide)).1 hhi
  simpa [Bounds.Encloses, tenthRoot] using And.intro hl hu.le

end Legendre.Arithmetic
