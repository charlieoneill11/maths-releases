import Legendre.Cosine
import Legendre.Arithmetic.Bounds

namespace Legendre

open scoped BigOperators

@[simp] theorem twelveMode_K : twelveMode.K = 2 := rfl

@[simp] theorem twelveMode_weight (j : Fin 12) : twelveMode.weight j = (twelveWeight j : ℝ) := rfl

theorem twelveMode_weightSum : twelveMode.weightSum = 0.755037 := by
  have h : (∑ j : Fin 12, |twelveWeight j|) = (0.755037 : ℚ) := by
    norm_num [Fin.sum_univ_succ, twelveWeight]
  have h' := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  simpa [CosineTest.weightSum, Rat.cast_sum] using h'

private theorem twelve_frequency_moment_two :
    (∑ j : Fin 12, |twelveMode.weight j| * (CosineTest.frequency j : ℝ) ^ 2) = 6.002901 := by
  have h : (∑ j : Fin 12, |twelveWeight j| * (CosineTest.frequency j : ℚ) ^ 2) =
      (6.002901 : ℚ) := by
    norm_num [Fin.sum_univ_succ, twelveWeight, CosineTest.frequency]
  have h' := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  simpa [Rat.cast_sum] using h'

private theorem pi_lt_3p142 : Real.pi < 3.142 := Real.pi_lt_d20.trans (by norm_num)

theorem twelveMode_polynomial_curvature (s : ℝ) :
    |deriv (deriv twelveMode.polynomial) s| ≤ 16 := by
  apply (twelveMode.abs_deriv_deriv_polynomial_le s).trans
  have heq : (∑ j : Fin 12, |twelveMode.weight j| * twelveMode.angularFrequency j ^ 2) =
      (Real.pi / 4) ^ 2 * ∑ j : Fin 12, |twelveMode.weight j| * (CosineTest.frequency j : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [CosineTest.angularFrequency, twelveMode_K]
    ring_nf
    rfl
  change (∑ j : Fin 12, |twelveMode.weight j| * twelveMode.angularFrequency j ^ 2) ≤ _
  rw [heq, twelve_frequency_moment_two]
  have hp := pow_le_pow_left₀ (div_nonneg Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 4))
    (div_le_div_of_nonneg_right pi_lt_3p142.le (by norm_num : (0 : ℝ) ≤ 4)) 2
  calc
    _ ≤ ((3.142 : ℝ) / 4) ^ 2 * 6.002901 := mul_le_mul_of_nonneg_right hp (by norm_num)
    _ ≤ _ := by norm_num

theorem twelveMode_F_curvature (y : ℝ) : |deriv (deriv twelveMode.F) y| ≤ 161 := by
  apply (twelveMode.abs_deriv_deriv_F_le y).trans
  rw [twelveMode_K, twelveMode_weightSum]
  have hp := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
    (mul_le_mul_of_nonneg_left pi_lt_3p142.le (by norm_num : (0 : ℝ) ≤ 2)) 2
  calc
    _ ≤ (2 * (3.142 : ℝ)) ^ 2 * (2 * 2 ^ 3 / 3) * 0.755037 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by norm_num)) (by norm_num)
    _ ≤ _ := by norm_num

end Legendre
