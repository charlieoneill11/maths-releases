import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.NormNum

namespace ZetaSixth

open Filter MeasureTheory

/-- The Riemann zeta function on the critical line. -/
noncomputable def zetaLine (t : ℝ) : ℂ :=
  riemannZeta ((1 : ℂ) / 2 + (t : ℂ) * Complex.I)

/-- The sixth moment of the Riemann zeta function on the critical line. -/
noncomputable def M6 (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖zetaLine t‖ ^ 6

/-- The local factor in the introduction of the paper, at a prime (p). -/
noncomputable def localFactor (p : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹) ^ 9 * ∑' j : ℕ, (Nat.choose (j + 2) 2 : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ j

noncomputable def a3 : ℝ := ∏' p : Nat.Primes, localFactor p

noncomputable def c3 : ℝ := a3 / (Nat.factorial 9 : ℝ)

/-- The exact normalized coefficient of Theorem 2. -/
def C : ℚ :=
  112666832560750258461501594014215737455802061 /
    2705696476246250148185796472625838239963136

/-- The eventual inequality of Theorem 2, for each coefficient strictly below (C). -/
def MainBound : Prop :=
  ∀ (c : ℝ), c < (C : ℝ) → ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T

theorem C_bounds : (416406 / 10000 : ℚ) < C ∧ C < 416407 / 10000 := by
  norm_num [C]

end ZetaSixth
