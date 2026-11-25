import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import HadwigerNelson.Placement.Height

/-! Horizontal slice estimates in Lemma 11. All distances and lengths are in physical units. -/

open MeasureTheory Set

namespace HadwigerNelson.Placement

noncomputable section

/-- Length of one horizontal slice of the intersection of a tile and its translate. -/
def sliceLength (left right : ℝ → ℝ) (D δ y : ℝ) : ℝ :=
  max 0 (min (right y) (right (y-δ) + D) - max (left y) (left (y-δ) + D))

/-- Integrated overlap for nonnegative vertical displacements. Beyond the tile height the two
open tiles are disjoint, including when the displacement equals their common height. -/
def sliceArea (left right : ℝ → ℝ) (H D δ : ℝ) : ℝ :=
  if H ≤ δ then 0 else ∫ y in δ..H, sliceLength left right D δ y

/-- Slice majorant used in each bin in Proposition 12. `lo ≥ H` gives an empty range. -/
def sliceUpper (left right : ℝ → ℝ) (H D lo hi : ℝ) : ℝ :=
  if H ≤ lo then 0 else
    ∫ y in lo..H, max 0 (right y - left (closestHeight H lo hi y) - D)

theorem sliceUpper_zero_left (right : ℝ → ℝ) (H D lo hi : ℝ) :
    sliceUpper (fun _ ↦ 0) right H D lo hi =
      if H ≤ lo then 0 else ∫ y in lo..H, max 0 (right y - D) := by
  simp [sliceUpper]

theorem sliceArea_le_sliceUpper {left right : ℝ → ℝ} {H D D₀ δ lo hi : ℝ}
    (hl : Continuous left) (hr : Continuous right)
    (hdown : AntitoneOn left (Icc 0 (H/2))) (hup : MonotoneOn left (Icc (H/2) H))
    (hlo : 0 ≤ lo) (hδ₀ : lo ≤ δ) (hδ₁ : δ ≤ hi) (hD : D₀ ≤ D) :
    sliceArea left right H D δ ≤ sliceUpper left right H D₀ lo hi := by
  by_cases h : H ≤ lo
  · simp [sliceArea, sliceUpper, h, h.trans hδ₀]
  rw [sliceUpper, if_neg h]
  have htarget : Continuous (fun y ↦ max 0 (right y - left (closestHeight H lo hi y) - D₀)) := by
    unfold closestHeight
    fun_prop
  by_cases hδ : H ≤ δ
  · rw [sliceArea, if_pos hδ]
    exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge h) (fun _ ↦ le_max_left _ _)
  rw [sliceArea, if_neg hδ]
  have hlength : Continuous (sliceLength left right D δ) := by
    unfold sliceLength
    fun_prop
  calc
    _ ≤ ∫ y in δ..H, max 0 (right y - left (closestHeight H lo hi y) - D₀) := by
      apply intervalIntegral.integral_mono_on (le_of_not_ge hδ) (hlength.intervalIntegrable _ _)
        (htarget.intervalIntegrable _ _)
      intro y hy
      apply max_le_max_left
      have hmin := closestHeight_minimizes hdown hup hlo hδ₀ hδ₁ hy.1 hy.2
      linarith [min_le_left (right y) (right (y-δ)+D), le_max_right (left y) (left (y-δ)+D)]
    _ ≤ _ := intervalIntegral.integral_mono_interval hδ₀ (le_of_not_ge hδ) le_rfl
      (.of_forall fun _ ↦ le_max_left _ _) (htarget.intervalIntegrable _ _)

end
end HadwigerNelson.Placement
