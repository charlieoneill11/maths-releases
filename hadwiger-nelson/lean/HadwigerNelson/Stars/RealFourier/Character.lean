import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.Ring

/-! Positive unit complex characters for physical angular displacements. -/

namespace HadwigerNelson.Stars
noncomputable section
open scoped BigOperators ComplexConjugate

def anglePhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem norm_anglePhase (θ : ℝ) : ‖anglePhase θ‖ = 1 := by
  simp [anglePhase, Complex.norm_exp, Complex.mul_re]

theorem anglePhase_add (x y : ℝ) : anglePhase (x+y) = anglePhase x * anglePhase y := by
  simp [anglePhase, add_mul, Complex.exp_add]

theorem anglePhase_neg (θ : ℝ) : anglePhase (-θ) = conj (anglePhase θ) := by
  simp only [anglePhase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg, neg_mul, mul_neg]

theorem anglePhase_period : Function.Periodic anglePhase (2*Real.pi) := by
  intro θ
  rw [anglePhase_add]
  simp [anglePhase, Complex.exp_two_pi_mul_I]

theorem anglePhase_continuous : Continuous anglePhase :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem anglePhase_shift (k : ℕ) (φ θ : ℝ) :
    anglePhase θ^k = conj (anglePhase φ^k) * anglePhase (θ+φ)^k := by
  conv_lhs => rw [show θ = -φ+(θ+φ) by ring,anglePhase_add,anglePhase_neg,mul_pow, ←map_pow]

end
end HadwigerNelson.Stars
