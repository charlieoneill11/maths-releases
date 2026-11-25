import Legendre.CosineTail
import Legendre.TwelveConstants

namespace Legendre

open Finset Set
open scoped BigOperators

theorem twelveMode_abs_deriv_core (y : ℝ) : |deriv twelveMode.F y| ≤ 19 := by
  apply (twelveMode.abs_deriv_F_le y).trans
  rw [twelveMode_K, twelveMode_weightSum]
  have hp : Real.pi < 3.142 := Real.pi_lt_d20.trans (by norm_num)
  linarith

private theorem twelveMode_abs_polynomial_deriv (s : ℝ) : |deriv twelveMode.polynomial s| ≤ 20 := by
  rw [twelveMode.deriv_polynomial]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin 12, |twelveMode.weight j| * 23 := by
      apply sum_le_sum
      intro j _
      have hj : CosineTest.frequency j ≤ 23 := by
        have hj : j.val < 12 := j.isLt
        unfold CosineTest.frequency
        omega
      have hfreq : (CosineTest.frequency j : ℝ) ≤ 23 := by exact_mod_cast hj
      have hp : Real.pi ≤ 4 := Real.pi_lt_d20.le.trans (by norm_num)
      have hω₀ : 0 ≤ twelveMode.angularFrequency j := by
        simp only [CosineTest.angularFrequency, twelveMode_K]
        positivity
      have hω : |twelveMode.angularFrequency j| ≤ 23 := by
        rw [abs_of_nonneg hω₀, CosineTest.angularFrequency, twelveMode_K]
        have h := mul_le_mul hp hfreq (by positivity) (by norm_num)
        linarith
      simp only [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans hω) (abs_nonneg _)
    _ = twelveMode.weightSum * 23 := by rw [← sum_mul]; rfl
    _ ≤ 20 := by rw [twelveMode_weightSum]; norm_num

private noncomputable def weightedPolynomial (s : ℝ) : ℝ := s * twelveMode.polynomial s

private theorem weightedPolynomial_deriv (s : ℝ) :
    deriv weightedPolynomial s = twelveMode.polynomial s + s * deriv twelveMode.polynomial s := by
  have hp : Differentiable ℝ twelveMode.polynomial := twelveMode.contDiff_polynomial.differentiable (by norm_num)
  have h := ((hasDerivAt_id s).mul (hp s).hasDerivAt).deriv
  simpa [weightedPolynomial, add_comm] using h

private theorem weightedPolynomial_deriv_deriv (s : ℝ) :
    deriv (deriv weightedPolynomial) s = 2 * deriv twelveMode.polynomial s +
      s * deriv (deriv twelveMode.polynomial) s := by
  have hp : Differentiable ℝ twelveMode.polynomial := twelveMode.contDiff_polynomial.differentiable (by norm_num)
  have hpp : Differentiable ℝ (deriv twelveMode.polynomial) := twelveMode.contDiff_polynomial.differentiable_deriv_two
  rw [show deriv weightedPolynomial = _ from funext weightedPolynomial_deriv]
  have h := ((hp s).hasDerivAt.add ((hasDerivAt_id s).mul (hpp s).hasDerivAt)).deriv
  convert h using 1
  simp only [id_eq, one_mul]
  ring

/-- A tail bound for the derivative obtained by two integrations by parts. -/
theorem twelveMode_abs_deriv_tail (y : ℝ) (hy : 16 ≤ y) : |deriv twelveMode.F y| ≤ 64 / y ^ 2 := by
  have h72 : ∀ s ∈ Icc (-twelveMode.K) twelveMode.K,
      |deriv (deriv (fun u ↦ u * twelveMode.polynomial u)) s| ≤ 72 := by
    intro s hs
    have hAbsS : |s| ≤ 2 := abs_le.mpr (by simpa only [twelveMode_K] using hs)
    change |deriv (deriv weightedPolynomial) s| ≤ 72
    rw [weightedPolynomial_deriv_deriv]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hProd := mul_le_mul hAbsS (twelveMode_polynomial_curvature s) (abs_nonneg _) (by norm_num)
    linarith [twelveMode_abs_polynomial_deriv s]
  have hp : |deriv weightedPolynomial twelveMode.K| ≤ 40 := by
    rw [weightedPolynomial_deriv, twelveMode.polynomial_pos_endpoint, zero_add, abs_mul, twelveMode_K,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [twelveMode_abs_polynomial_deriv 2]
  have hn : |deriv weightedPolynomial (-twelveMode.K)| ≤ 40 := by
    rw [weightedPolynomial_deriv, twelveMode.polynomial_neg_endpoint, zero_add, abs_mul, twelveMode_K,
      abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [twelveMode_abs_polynomial_deriv (-2)]
  have h := twelveMode.sq_mul_abs_deriv_F_bound 72 h72 y
  change y ^ 2 * |deriv twelveMode.F y| ≤
    (|deriv weightedPolynomial twelveMode.K| + |deriv weightedPolynomial (-twelveMode.K)| +
      72 * (twelveMode.K - (-twelveMode.K))) / (2 * Real.pi) at h
  have hπ : (3 : ℝ) ≤ Real.pi := Real.pi_gt_d20.le.trans' (by norm_num)
  have h64 : (|deriv weightedPolynomial twelveMode.K| + |deriv weightedPolynomial (-twelveMode.K)| +
      72 * (twelveMode.K - (-twelveMode.K))) / (2 * Real.pi) ≤ 64 := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [twelveMode_K] at hp hn ⊢
    linarith
  exact (le_div_iff₀ (pow_pos (by linarith) 2)).mpr (by simpa only [mul_comm] using h.trans h64)

end Legendre
