import Chowla.CountingMassSieve
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace Chowla

open scoped ArithmeticFunction.Moebius BigOperators

private theorem trivial_mod_two_apply (n : ℕ) :
    (1 : DirichletCharacter ℂ 2) (n : ZMod 2) = if Odd n then 1 else 0 := by
  have hunit : IsUnit (n : ZMod 2) ↔ Odd n := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.prime_two.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero, Nat.odd_iff]
    omega
  by_cases h : Odd n
  · rw [if_pos h]
    exact MulChar.one_apply (hunit.mpr h)
  · rw [if_neg h]
    exact MulChar.map_nonunit _ (hunit.not.mpr h)

private theorem trivial_mod_two_LSeries :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 2) (n : ZMod 2)) 2 =
      ((Real.pi^2 / 8 : ℝ) : ℂ) := by
  have hRe : 1 < (2 : ℂ).re := by norm_num
  rw [← DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ 2) hRe]
  change DirichletCharacter.LFunctionTrivChar 2 2 = _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num), riemannZeta_two]
  rw [Nat.Prime.primeFactors Nat.prime_two, Finset.prod_singleton, Nat.cast_ofNat]
  have hpow : (2 : ℂ) ^ (-(2 : ℂ)) = 1/4 := by
    rw [Complex.cpow_neg, ← Nat.cast_ofNat (R := ℂ) (n := 2), Complex.cpow_natCast]
    norm_num
  simp only [hpow, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

private theorem trivial_mod_two_twistedMoebius_LSeries :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 2) (n : ZMod 2) * (μ n : ℂ)) 2 =
       ((∑' n, oddMoebiusTerm n : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  congr with n
  unfold LSeries.term
  by_cases hn : n = 0
  · subst n
    simp [oddMoebiusTerm]
  · simp only [if_neg hn]
    rw [trivial_mod_two_apply]
    by_cases h : Odd n
    · rw [if_pos h, one_mul, oddMoebiusTerm, if_pos h]
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast
      rfl
    · rw [if_neg h, zero_mul, oddMoebiusTerm, if_neg h, Complex.ofReal_zero, zero_div]

theorem oddMoebiusTerm_tsum :
    (∑' a, oddMoebiusTerm a) = 8 / Real.pi^2 := by
  have hRe : 1 < (2 : ℂ).re := by norm_num
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ 2) hRe
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 2) (n : ZMod 2)) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 2) (n : ZMod 2) * (μ n : ℂ)) 2 = 1 at h
  rw [trivial_mod_two_LSeries, trivial_mod_two_twistedMoebius_LSeries] at h
  have hreal := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re] at hreal
  have hp : Real.pi ^ 2 / 8 ≠ 0 := by positivity
  calc
    (∑' a, oddMoebiusTerm a) = 1 / (Real.pi^2 / 8) := (eq_div_iff hp).2 (by linarith only [hreal, mul_comm (Real.pi ^ 2 / 8) (∑' a, oddMoebiusTerm a)])
    _ = 8 / Real.pi^2 := by field_simp [Real.pi_ne_zero]

end Chowla
