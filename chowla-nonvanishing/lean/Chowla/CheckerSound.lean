import Chowla.CheckerArithmetic
import Chowla.Enclosure
import Chowla.SplineProfiles
import Chowla.SplineCovariance
import Mathlib.Algebra.BigOperators.Ring.List

namespace Chowla.Checker

open MeasureTheory Set
open scoped BigOperators

theorem splinePrimitives_sound (p : Spline) (n : ℕ) (x : ℚ) :
    (splinePrimitives p n x : ℝ) = lowerPrimitive n p.toReal x := by
  unfold splinePrimitives
  rw [Spline.eval_sound, Spline.primitive_sound]

theorem mean_sound (p : Spline) :
    (mean (splinePrimitives p) : ℝ) =
      p.toReal 0 - (lowerPrimitive 1 p.toReal 1 - lowerPrimitive 1 p.toReal 0) := by
  simp only [mean, Rat.cast_sub, splinePrimitives_sound]
  norm_num [lowerPrimitive]

theorem covariance_primitive_sound (p : Spline) (t : ℚ) :
    (covariance (splinePrimitives p) t : ℝ) =
      4 * ((t : ℝ) * lowerPrimitive 1 p.toReal t - lowerPrimitive 2 p.toReal t +
        lowerPrimitive 2 p.toReal 0) -
      2 * (lowerPrimitive 2 p.toReal (1 + t) - 2 * lowerPrimitive 2 p.toReal 1 +
        lowerPrimitive 2 p.toReal (1 - t)) := by
  simp only [covariance, triangle, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    splinePrimitives_sound]
  norm_num

private theorem horner_eq_sum (cs : ℕ → ℚ) (n : ℕ) (x : ℚ) :
    ((List.range n).map cs).foldr (fun c rest => c + x * rest) 0 =
      ((List.range n).map (fun j => cs j * x ^ j)).sum := by
  induction n generalizing cs with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons, List.sum_cons,
      pow_zero, mul_one]
    rw [ih (cs ∘ Nat.succ)]
    rw [← List.sum_map_mul_left]
    congr 2
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, pow_succ]
    ring

private theorem ratCast_sum_range (n : ℕ) (f : ℕ → ℚ) :
    (((List.range n).map f).sum : ℝ) =
      ∑ i ∈ Finset.range n, (f i : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add, ih, Finset.sum_range_succ]
    simp

theorem oddPrimitive_formula (p : Spline) (n : ℕ) (x : ℚ) :
    (oddPrimitive (splinePrimitives p) n x : ℝ) =
      if (x : ℝ) < 0 then -lowerPrimitive n p.toReal x
      else lowerPrimitive n p.toReal x -
        2 * ∑ i ∈ Finset.range n, (x : ℝ) ^ i / i.factorial *
          lowerPrimitive (n - i) p.toReal 0 := by
  unfold oddPrimitive evaluateOddPrimitive oddPrimitiveCoefficients
  have hcast : (x : ℝ) < 0 ↔ x < 0 := by exact_mod_cast Iff.rfl
  by_cases h : x < 0
  · rw [if_pos h, if_pos (hcast.mpr h), Rat.cast_neg, splinePrimitives_sound]
  · rw [if_neg h, if_neg (hcast.not.mpr h), Rat.cast_sub, Rat.cast_mul, splinePrimitives_sound,
      horner_eq_sum, ratCast_sum_range]
    norm_num only [Rat.cast_ofNat]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    rw [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, splinePrimitives_sound]
    norm_num only [Rat.cast_zero]
    ring

noncomputable def realShiftDifference (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * f x - f (x + a) - f (x - a)

theorem cast_shiftFold (widths : List ℚ) (f : ℚ → ℚ) (F : ℝ → ℝ)
    (hf : ∀ x : ℚ, (f x : ℝ) = F x) (x : ℚ) :
    ((widths.foldr shiftDifference f) x : ℝ) =
      (((widths.map (fun a : ℚ => (a : ℝ))).foldr realShiftDifference F) (x : ℝ)) := by
  induction widths generalizing x with
  | nil => exact hf x
  | cons a as ih =>
    simp only [List.foldr_cons, List.map_cons, shiftDifference, realShiftDifference,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    rw [ih, ih, ih, Rat.cast_add, Rat.cast_sub]

noncomputable def realOddPrimitive (h : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then -lowerPrimitive n h x
  else lowerPrimitive n h x -
    2 * ∑ i ∈ Finset.range n, x ^ i / i.factorial * lowerPrimitive (n - i) h 0

/-- Algebraic soundness of the higher marked term as the formula of Lemma 28. -/
theorem markedCumulant_higher_formula (p : Spline) (a b : ℚ) (as : List ℚ) :
    let widths := a :: b :: as
    let n := widths.length + 1
    (markedCumulant (splinePrimitives p) widths : ℝ) =
      (-2 : ℝ) ^ n / 2 *
        (((widths.map fun t : ℚ => (t : ℝ)).foldr realShiftDifference (realOddPrimitive p.toReal n)) 1) := by
  let widths := a :: b :: as
  let n := widths.length + 1
  change ((cumulantFactor n * shiftSum (shiftWeights widths)
      (oddPrimitive (splinePrimitives p) n) 1 : ℚ) : ℝ) = _
  rw [Rat.cast_mul, shiftWeights_sound]
  rw [cast_shiftFold widths _ (realOddPrimitive p.toReal n) (oddPrimitive_formula p n)]
  simp only [cumulantFactor, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  norm_num only [Rat.cast_one]
  rfl

theorem markedCumulant_higher_sound (p : Spline) (a b : ℚ) (as : List ℚ)
    (hp : IsProfile p.toReal)
    (hwidths : ∀ t ∈ a :: b :: as, (t : ℝ) ∈ Ioc 0 1) :
    (markedCumulant (splinePrimitives p) (a :: b :: as) : ℝ) =
      cumulant (p.toReal :: (a :: b :: as).map (fun t : ℚ => rectangle (t : ℝ))) := by
  let widths := a :: b :: as
  let ar := widths.map fun t : ℚ => (t : ℝ)
  let n := widths.length + 1
  have har : ∀ t ∈ ar, t ∈ Ioc 0 1 := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact hwidths q hq
  have hlen : 2 ≤ ar.length := by simp [ar, widths]
  have hodd : realOddPrimitive p.toReal n = lowerPrimitive n (oddProfile p.toReal) := by
    funext x
    exact (lowerPrimitive_oddProfile p.toReal hp n (Nat.succ_pos _) x).symm
  rw [markedCumulant_higher_formula]
  change (-2 : ℝ) ^ n / 2 * (ar.foldr realShiftDifference (realOddPrimitive p.toReal n)) 1 =
    cumulant (p.toReal :: widths.map (fun t : ℚ => rectangle (t : ℝ)))
  rw [hodd]
  have h := cumulant_shift p.toReal hp ar har hlen
  simpa only [n, ar, List.length_map, List.map_map, Function.comp_def, realShiftDifference,
    Chowla.shiftDifference] using h.symm

theorem mean_cumulant_sound (p : Spline) (hp : IsProfile p.toReal) :
    (mean (splinePrimitives p) : ℝ) = cumulant [p.toReal] := by
  rw [mean_sound, cumulant,
    definite_eq_lowerPrimitive_sub (integrable_of_isProfile hp)]

theorem covariance_cumulant_sound (p : Spline) (hp : IsProfile p.toReal) (t : ℚ)
    (ht : (t : ℝ) ∈ Ioc 0 1) :
    (covariance (splinePrimitives p) t : ℝ) = cumulant [p.toReal, rectangle t] := by
  rw [covariance_primitive_sound, cumulant_covariance p.toReal hp t ht,
    weighted_integral_eq_primitives hp ht.1.le, triangular_integral_eq_primitives hp ht.1.le]

/-- Exact evaluation of the marked cumulant. -/
theorem markedCumulant_sound (p : Spline) (widths : List ℚ) (hp : IsProfile p.toReal)
    (hwidths : ∀ t ∈ widths, (t : ℝ) ∈ Ioc 0 1) :
    (markedCumulant (splinePrimitives p) widths : ℝ) =
      cumulant (p.toReal :: widths.map (fun t : ℚ => rectangle (t : ℝ))) := by
  cases widths with
  | nil => exact mean_cumulant_sound p hp
  | cons a as =>
    cases as with
    | nil => exact covariance_cumulant_sound p hp a (hwidths a (by simp))
    | cons b bs => exact markedCumulant_higher_sound p a b bs hp hwidths

private theorem realHorner_range (cs : ℕ → ℚ) (n : ℕ) (x : ℝ) :
    Spline.Coefficients.toReal ((List.range n).map cs) x =
      ∑ i ∈ Finset.range n, (cs i : ℝ) * x ^ i := by
  induction n generalizing cs with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, Spline.Coefficients.toReal_cons, List.map_map, ih]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    rw [Finset.mul_sum, add_comm ((cs 0 : ℚ) : ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.comp_apply, pow_succ]
    ring

private theorem hstarCoefficients_sound (x : ℝ) :
    hstarCoefficients.toReal x =
      (HstarFactorQ : ℝ) * trigTaylor 0 7 (x / 2) +
        (1/4 - (HstarFactorQ : ℝ)) * trigTaylor 1 6 (x / 2) := by
  rw [hstarCoefficients, realHorner_range]
  norm_num [HstarFactorQ, trigTaylor, trigTerm, Finset.sum_range_succ, Nat.factorial]
  ring

/-- The exact piecewise spline has the same real profile as the paper's Taylor enclosure
away from the endpoint, which is enough for convolution. -/
theorem hstarSpline_sound : hstarSpline.toReal =ᵐ[volume] Hstar := by
  filter_upwards [(volume : Measure ℝ).ae_ne (1 : ℝ)] with x hx
  unfold hstarSpline
  rw [Spline.toReal_append, Spline.piece_sound _ _ _ (by norm_num),
    Spline.piece_sound _ _ _ (by norm_num)]
  simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_zero, Hstar, Set.indicator_apply]
  by_cases hneg : x < 0
  · have hposFalse : ¬ (0 : ℝ) ≤ x := not_le.mpr hneg
    have hIcc : x ∈ Icc (-1 : ℝ) 1 ↔ -1 ≤ x :=
      ⟨fun h => h.1, fun h => ⟨h, le_trans hneg.le zero_le_one⟩⟩
    simp only [mem_Ico, hneg, and_true, hposFalse, false_and, if_false, add_zero, hIcc]
    split_ifs
    · rw [Spline.Coefficients.toReal_scaleInput, hstarCoefficients_sound, abs_of_neg hneg]
      norm_num only [Rat.cast_neg, Rat.cast_one, neg_one_mul]
    · rfl
  · have hpos : 0 ≤ x := not_lt.mp hneg
    have hIcc : x ∈ Icc (-1 : ℝ) 1 ↔ x < 1 := by
      constructor
      · exact fun h => lt_of_le_of_ne h.2 hx
      · exact fun h => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hpos, h.le⟩
    simp only [mem_Ico, hneg, and_false, if_false, zero_add, hpos, true_and, hIcc]
    split_ifs
    · rw [hstarCoefficients_sound, abs_of_nonneg hpos]
    · rfl

end Chowla.Checker
