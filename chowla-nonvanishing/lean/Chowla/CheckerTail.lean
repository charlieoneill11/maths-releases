import Chowla.CheckerSound
import Chowla.EnclosureProofs

namespace Chowla.Checker

open MeasureTheory Set

theorem cast_width_sum (widths : List ℚ) :
    ((widths.sum : ℚ) : ℝ) = (widths.map (fun a : ℚ => (a : ℝ))).sum := by
  induction widths with
  | nil => simp
  | cons a as ih => simp [List.sum_cons, Rat.cast_add, ih]

private theorem rectangle_support_bound (a : ℝ) (ha : 0 ≤ a) :
    HasRadiusAtMost (rectangle a) a := by
  refine ⟨ha, ?_⟩
  filter_upwards with u hu
  exact Set.indicator_of_notMem hu _

private theorem forall₂_rectangle (A : List ℝ) (hA : ∀ a ∈ A, 0 ≤ a) :
    List.Forall₂ HasRadiusAtMost (A.map rectangle) A := by
  induction A with
  | nil => exact .nil
  | cons a as ih =>
    exact .cons (rectangle_support_bound a (hA a (by simp)))
      (ih fun b hb => hA b (by simp [hb]))

private theorem cast_positive_part (x : ℚ) :
    ((max x (0 : ℚ) : ℚ) : ℝ) = max (x : ℝ) 0 := by
  by_cases h : x ≤ 0
  · have hr : (x : ℝ) ≤ 0 := by exact_mod_cast h
    rw [max_eq_right h, Rat.cast_zero, max_eq_right hr]
  · have hq : 0 ≤ x := le_of_not_ge h
    have hr : 0 ≤ (x : ℝ) := by exact_mod_cast hq
    rw [max_eq_left hq, max_eq_left hr]

/-- The fast signed-rectangle evaluator agrees with the unmarked cumulant tail. -/
theorem rectangleTail_sound (widths : List ℚ) (hwidths : ∀ a ∈ widths, 0 < a)
    (hlen : 2 ≤ widths.length) :
    (rectangleTail widths : ℝ) =
      delta (widths.map fun a : ℚ => rectangle (a : ℝ)) := by
  let A := widths.map fun a : ℚ => (a : ℝ)
  have hA : ∀ a ∈ A, 0 < a := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    exact_mod_cast hwidths q hq
  have hlenA : 2 ≤ A.length := by simpa [A] using hlen
  have he : (widths.map fun a : ℚ => rectangle (a : ℝ)) = A.map rectangle := by
    simp [A, List.map_map, Function.comp_def]
  rw [he]
  by_cases h : widths.sum ≤ 1
  · have hsum : A.sum ≤ 1 := by
      rw [← cast_width_sum]
      exact_mod_cast h
    have hs := delta_eq_zero_of_support (A.map rectangle) A
      (by
        intro f hf
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
        exact rectangle_isProfile a)
      (forall₂_rectangle A fun a ha => (hA a ha).le) hsum
    rw [hs]
    simp [rectangleTail, h]
  · rw [delta_rectangles_shift A hA hlenA]
    simp only [rectangleTail, Nat.not_lt.mpr hlen, h, decide_false, Bool.or_self, Bool.false_eq_true,
      if_false, Rat.cast_mul, shiftWeights_sound, A, List.length_map]
    rw [cast_shiftFold widths _ (fun x : ℝ =>
      (max x 0) ^ widths.length / widths.length.factorial)]
    · simp only [cumulantFactor, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat,
        Rat.cast_one]
      rfl
    · intro t
      simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, cast_positive_part]

end Chowla.Checker
