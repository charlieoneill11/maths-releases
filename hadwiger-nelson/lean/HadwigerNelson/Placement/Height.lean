import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

/-! The least lower-profile value over a bin of vertical displacements in Lemma 11. -/

open Set

namespace HadwigerNelson.Placement

noncomputable section

/-- A height in the range of possible displaced profiles nearest the midpoint of the tile. -/
def closestHeight (H lo hi y : ℝ) : ℝ := max (y - hi) (min (H/2) (y - lo))

/-- Unimodality of the lower boundary shows that the height in Lemma 11 minimizes its value. -/
theorem closestHeight_minimizes {left : ℝ → ℝ} {H lo δ hi y : ℝ}
    (hdown : AntitoneOn left (Icc 0 (H/2))) (hup : MonotoneOn left (Icc (H/2) H))
    (hlo : 0 ≤ lo) (hδ₀ : lo ≤ δ) (hδ₁ : δ ≤ hi) (hy₀ : δ ≤ y) (hy₁ : y ≤ H) :
    left (closestHeight H lo hi y) ≤ left (y - δ) := by
  have hends : y - hi ≤ y - lo := by linarith
  by_cases hbelow : y - lo ≤ H/2
  · rw [closestHeight, min_eq_right hbelow, max_eq_right hends]
    apply hdown <;> first | constructor <;> linarith | linarith
  · rw [closestHeight, min_eq_left (le_of_not_ge hbelow)]
    by_cases habove : H/2 ≤ y - hi
    · rw [max_eq_left habove]
      apply hup <;> first | constructor <;> linarith | linarith
    · rw [max_eq_right (le_of_not_ge habove)]
      by_cases h : y - δ ≤ H/2
      · apply hdown <;> first | constructor <;> linarith | linarith
      · apply hup <;> first | constructor <;> linarith | linarith

end
end HadwigerNelson.Placement
