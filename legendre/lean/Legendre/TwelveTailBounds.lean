import Legendre.CosineTail
import Legendre.TwelveConstants

namespace Legendre

open Finset
open scoped BigOperators

private noncomputable def ν (j : Fin 12) : ℝ := CosineTest.frequency j

private noncomputable def α (j : Fin 12) : ℝ := (-1 : ℝ) ^ j.val * ν j * (twelveWeight j : ℝ)

private noncomputable def tailLambda : ℝ := 1 - ((23 : ℝ) / 128) ^ 2

private theorem ν_nonneg (j : Fin 12) : 0 ≤ ν j := by unfold ν; positivity

private theorem ν_le (j : Fin 12) : ν j ≤ 23 := by
  unfold ν CosineTest.frequency
  exact_mod_cast (show 2 * j.val + 1 ≤ 23 by omega)

private theorem sum_alpha : (∑ j : Fin 12, α j) = 0.000003 := by
  have h : (∑ j : Fin 12, (-1 : ℚ) ^ j.val * (CosineTest.frequency j : ℚ) * twelveWeight j) =
      (0.000003 : ℚ) := by norm_num [Fin.sum_univ_succ, twelveWeight, CosineTest.frequency]
  have h' := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  simpa [α, ν, Rat.cast_sum] using h'

private theorem sum_abs_alpha_mul_freq_sq : (∑ j : Fin 12, |α j| * (ν j) ^ 2) = 37.970655 := by
  have h : (∑ j : Fin 12, |twelveWeight j| * (CosineTest.frequency j : ℚ) ^ 3) =
      (37.970655 : ℚ) := by norm_num [Fin.sum_univ_succ, twelveWeight, CosineTest.frequency]
  have h' := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  push_cast at h'
  rw [← h']
  apply sum_congr rfl
  intro j _
  simp only [α, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ν]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  ring

private theorem tailLambda_pos : 0 < tailLambda := by norm_num [tailLambda]

private theorem tail_denominator {y : ℝ} (hy : 16 ≤ y) (j : Fin 12) :
    tailLambda * (8 * y) ^ 2 ≤ (8 * y) ^ 2 - (ν j) ^ 2 := by
  have h : ν j ≤ (23 / 128 : ℝ) * (8 * y) := (ν_le j).trans (by linarith)
  have hpow := pow_le_pow_left₀ (ν_nonneg j) h 2
  unfold tailLambda
  rw [mul_pow] at hpow
  linarith

private theorem tail_denominator_pos {y : ℝ} (hy : 16 ≤ y) (j : Fin 12) :
    0 < (8 * y) ^ 2 - (ν j) ^ 2 :=
  (mul_pos tailLambda_pos (pow_pos (mul_pos (by norm_num) (by linarith)) 2)).trans_le (tail_denominator hy j)

private theorem twelveMode_F_tail_closed (y : ℝ) (hy : 16 ≤ y) :
    twelveMode.F y = 8 / Real.pi * Real.cos (4 * Real.pi * y) *
      ∑ j : Fin 12, α j / ((ν j) ^ 2 - (8 * y) ^ 2) := by
  rw [twelveMode.F_eq_closed_form]
  · simp only [twelveMode_K, twelveMode_weight, show (4 : ℝ) * 2 = 8 by norm_num, α, ν]
    rw [show 2 * Real.pi * 2 * y = 4 * Real.pi * y by ring]
    rfl
  · intro j
    rw [twelveMode_K, show (4 : ℝ) * 2 = 8 by norm_num]
    change (ν j) ^ 2 ≠ (8 * y) ^ 2
    exact (sub_pos.mp (tail_denominator_pos hy j)).ne

private theorem cancelled_sum_estimate (y : ℝ) (hy : 16 ≤ y) :
    |∑ j : Fin 12, α j / ((ν j) ^ 2 - (8 * y) ^ 2)| ≤
      0.000003 / (8 * y) ^ 2 + 37.970655 / (tailLambda * (8 * y) ^ 4) := by
  let X := 8 * y
  have hX : 0 < X := by dsimp [X]; linarith
  have hden (j : Fin 12) : (ν j) ^ 2 - X ^ 2 ≠ 0 := by
    have h := tail_denominator_pos hy j
    exact sub_ne_zero.mpr (sub_pos.mp h).ne
  have hsplit (j : Fin 12) : α j / ((ν j) ^ 2 - X ^ 2) =
      -(α j / X ^ 2) - α j * (ν j) ^ 2 / (X ^ 2 * (X ^ 2 - (ν j) ^ 2)) := by
    have hden' : X ^ 2 - (ν j) ^ 2 ≠ 0 := (tail_denominator_pos hy j).ne'
    field_simp [hX.ne', hden j, hden']
    ring
  change |∑ j : Fin 12, α j / ((ν j) ^ 2 - X ^ 2)| ≤ 0.000003 / X ^ 2 + 37.970655 / (tailLambda * X ^ 4)
  simp_rw [hsplit]
  rw [sum_sub_distrib, sum_neg_distrib, ← sum_div, sum_alpha]
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 0.000003 / X ^ 2 by positivity)]
  · rw [← sum_abs_alpha_mul_freq_sq, sum_div]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    change |α j * (ν j) ^ 2 / (X ^ 2 * (X ^ 2 - (ν j) ^ 2))| ≤ _
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (ν j)),
      abs_of_pos (mul_pos (pow_pos hX 2) (tail_denominator_pos hy j))]
    apply div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (mul_pos tailLambda_pos (pow_pos hX 4))
    calc
      _ = X ^ 2 * (tailLambda * X ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_denominator hy j) (sq_nonneg _)

theorem twelveMode_abs_F_tail (y : ℝ) (hy : 16 ≤ y) :
    |twelveMode.F y| ≤ (0.00000012 : ℝ) / y ^ 2 + 0.0244 / y ^ 4 := by
  have hy' : 0 < y := by linarith
  have hπ : (3.14159 : ℝ) ≤ Real.pi := (by norm_num : (3.14159 : ℝ) ≤ 3.14159265358979323846)
    |>.trans Real.pi_gt_d20.le
  have hs : 8 / Real.pi ≤ (8 : ℝ) / 3.14159 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ
  rw [twelveMode_F_tail_closed y hy, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ (8 : ℝ) / Real.pi by positivity)]
  have hFactor : 8 / Real.pi * |Real.cos (4 * Real.pi * y)| ≤ (8 : ℝ) / 3.14159 :=
    (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans hs
  have hnonneg : 0 ≤ (0.000003 : ℝ) / (8 * y) ^ 2 + 37.970655 / (tailLambda * (8 * y) ^ 4) := by
    have h := tailLambda_pos
    positivity
  calc
    _ ≤ ((8 : ℝ) / 3.14159) * (0.000003 / (8 * y) ^ 2 + 37.970655 / (tailLambda * (8 * y) ^ 4)) :=
      mul_le_mul hFactor (cancelled_sum_estimate y hy) (abs_nonneg _) (by norm_num)
    _ = (8 * 0.000003 / (3.14159 * 64) : ℝ) / y ^ 2 +
        (8 * 37.970655 / (3.14159 * tailLambda * 4096) : ℝ) / y ^ 4 := by
      field_simp [hy'.ne', tailLambda_pos.ne']
      ring
    _ ≤ _ := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
      · exact div_le_div_of_nonneg_right (by norm_num [tailLambda]) (by positivity)

end Legendre
