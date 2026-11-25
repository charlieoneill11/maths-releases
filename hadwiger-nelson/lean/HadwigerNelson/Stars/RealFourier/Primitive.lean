import HadwigerNelson.Stars.RealFourier.Character
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace HadwigerNelson.Stars
open MeasureTheory

/-- Exact positive-frequency integral on a single arc. Certificate endpoint sums
are accumulated as start minus stop, giving the purely imaginary factor I/k. -/
theorem integral_anglePhase_pow (a b : ℝ) (k : ℕ) (hk : 0 < k) :
    (∫ θ in a..b, anglePhase θ ^ k) =
      Complex.I * (anglePhase a ^ k - anglePhase b ^ k) / (k : ℂ) := by
  let c : ℂ := (k : ℂ) * Complex.I
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : c ≠ 0 := mul_ne_zero hk' Complex.I_ne_zero
  have form (θ : ℝ) : anglePhase θ ^ k = Complex.exp (c * (θ : ℂ)) := by
    rw [anglePhase, ← Complex.exp_nat_mul]
    congr 1
    dsimp only [c]
    ring
  have deriv (θ : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c)
      (Complex.exp (c * θ)) θ := by
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * θ)) hc]
    apply ((Complex.hasDerivAt_exp _).comp θ _).div_const c
    simpa only [mul_one] using ((hasDerivAt_id (θ : ℂ)).const_mul c).comp_ofReal
  simp_rw [form]
  have cont : Continuous (fun θ : ℝ => Complex.exp (c * θ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => deriv θ)
    (cont.intervalIntegrable _ _)]
  simp only [c, div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring

end HadwigerNelson.Stars
