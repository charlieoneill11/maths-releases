import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators

/-! All sources related by a global rotation or reflection have the same
power-sum magnitudes, as required to transport the rectangle estimates. -/

namespace HadwigerNelson.Stars
open scoped BigOperators ComplexConjugate

theorem normPowerSum_rotate {d : Nat} (z : Fin d → ℂ) (u : ℂ) (hu : ‖u‖ = 1) (k : Nat) :
    ‖∑ j, (u*z j)^k‖ = ‖∑ j, z j^k‖ := by
  simp only [mul_pow,←Finset.mul_sum,Complex.norm_mul,Complex.norm_pow,hu,one_pow,one_mul]

theorem normPowerSum_mirror {d : Nat} (z : Fin d → ℂ) (u : ℂ) (hu : ‖u‖ = 1) (k : Nat) :
    ‖∑ j, (u*conj (z j))^k‖ = ‖∑ j, z j^k‖ := by
  rw [normPowerSum_rotate (fun j => conj (z j)) u hu k]
  simp only [←map_pow,←map_sum,Complex.norm_conj]

end HadwigerNelson.Stars
