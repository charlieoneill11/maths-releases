import Legendre.Cited
import Legendre.Statement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Legendre

open MeasureTheory
open scoped BigOperators

/-- A natural prime lies strictly between two real endpoints. -/
def PrimeIn (a b : ℝ) : Prop := ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) < b

/-- Definition 12 of the paper. -/
structure CosineTest where
  K : ℝ
  K_pos : 0 < K
  modes : ℕ
  modes_pos : 0 < modes
  weight : Fin modes → ℝ

namespace CosineTest

def frequency {modes : ℕ} (j : Fin modes) : ℕ := 2 * j.val + 1

noncomputable def polynomial (g : CosineTest) (s : ℝ) : ℝ :=
  ∑ j, g.weight j * Real.cos (Real.pi * frequency j * s / (2 * g.K))

noncomputable def G (g : CosineTest) : ℝ → ℝ :=
  Set.indicator (Set.Icc (-g.K) g.K) g.polynomial

noncomputable def positivePart (g : CosineTest) (s : ℝ) : ℝ := max (g.G s) 0

noncomputable def F (g : CosineTest) (y : ℝ) : ℝ :=
  ∫ s in -g.K..g.K, g.polynomial s * Real.cos (2 * Real.pi * y * s)

noncomputable def complexF (g : CosineTest) (y : ℂ) : ℂ :=
  ∫ s in -g.K..g.K, (g.polynomial s : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * y * (s : ℂ))

noncomputable def weightSum (g : CosineTest) : ℝ := ∑ j, |g.weight j|

noncomputable def mass (g : CosineTest) : ℝ := ∫ s, |g.G s|

end CosineTest

noncomputable def logPlus (t : ℝ) : ℝ := max (Real.log t) 0

noncomputable def fourierMass (F : ℝ → ℝ) : ℝ := ∫ y, |F y|

noncomputable def logMoment (F : ℝ → ℝ) : ℝ := ∫ y, |F y| * Real.log |y|

noncomputable def totalVariation (F : ℝ → ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), |deriv F y|

noncomputable def logVariation (F : ℝ → ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), logPlus y * |deriv F y|

noncomputable def zeroCountMain (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) + 7 / 8

/-- The centre and half-width on the logarithmic scale. -/
structure Window where
  a : ℝ
  D : ℝ

namespace Window

noncomputable def ofBase (x : ℝ) : Window :=
  ⟨(x * (x + 1)) ^ ((11 : ℝ) / 10), (11 / 10 : ℝ) * Real.log (1 + 1 / x)⟩

noncomputable def P (w : Window) : ℝ := w.D * Real.sqrt w.a

noncomputable def L (w : Window) : ℝ := Real.log (Real.sqrt w.a)

noncomputable def W (w : Window) : ℝ := w.a * w.D

noncomputable def Δ (w : Window) : ℝ := w.D / (2 * Real.pi)

noncomputable def endpoint (w : Window) (s : ℝ) : ℝ := w.a * Real.exp (w.D * s)

noncomputable def scale (w : Window) (t : ℝ) : ℝ := Real.log (t / w.a) / w.D

end Window

noncomputable def U : ℝ := 1 + 1 / 10 ^ 12

noncomputable def U₁ : ℝ := 1 + 1 / 10 ^ 10

/-- Hypotheses on the window in Proposition 17. -/
structure WindowBounds (w : Window) (K : ℝ) : Prop where
  a_pos : 0 < w.a
  D_pos : 0 < w.D
  log_a : 60 ≤ Real.log w.a
  width : K * w.D ≤ (U - 1) / U
  scale : K * w.P < 100

noncomputable def weightedZeroNorm (F : ℝ → ℝ) (D : ℝ) (ρ : nontrivialZeros) : ℝ :=
  (zeroMultiplicity ρ : ℝ) * |F (D / (2 * Real.pi) * (ρ : ℂ).im)|

noncomputable def weightedZeroTerm (w : Window) (g : CosineTest) (ρ : nontrivialZeros) : ℝ :=
  (zeroMultiplicity ρ : ℝ) * g.F (w.Δ * (ρ : ℂ).im) *
    Real.cos ((ρ : ℂ).im * Real.log w.a)

noncomputable def primePowerSum (w : Window) (g : CosineTest) : ℝ :=
  ∑ m ∈ Finset.range (⌊w.endpoint g.K⌋₊ + 1),
    ArithmeticFunction.vonMangoldt m / Real.sqrt (m : ℝ) * g.G (w.scale m)

noncomputable def trivialZeroTerm (w : Window) (g : CosineTest) (k : ℕ) : ℝ :=
  let r := 2 * ((k : ℝ) + 1) + 1 / 2
  w.a ^ (-r) * ∫ s in -g.K..g.K, g.polynomial s * Real.exp (-r * w.D * s)

noncomputable def poleTerm (w : Window) (g : CosineTest) : ℝ :=
  w.P * ∫ s in -g.K..g.K, g.polynomial s * Real.cosh (w.D * s / 2)

noncomputable def shoulderSum (w : Window) (g : CosineTest) : ℝ := by
  classical
  exact ∑ p ∈ (Finset.range (⌊w.endpoint g.K⌋₊ + 1)).filter
      (fun p : ℕ ↦ p.Prime ∧ 1 < |w.scale p| ∧ |w.scale p| ≤ g.K),
    Real.log p / Real.sqrt (p : ℝ) * g.positivePart (w.scale p)

noncomputable def primePowerError (w : Window) (K : ℝ) : ℝ :=
  let ell := Real.log w.a + K * w.D
  (2 + ell / Real.log 2 * (1 + K * w.P * U)) * ell * U / Real.sqrt w.a

def twelveWeight (j : Fin 12) : ℚ :=
  (#[462994, 232962, 17574, -31174, 472, 7016, -1460, -974, 377, -20, 3, -11][j] : ℚ) / 10 ^ 6

noncomputable def twelveMode : CosineTest :=
  ⟨2, by norm_num, 12, by decide, fun j ↦ twelveWeight j⟩

structure TwelveModeEstimates : Prop where
  at_zero : 1.00000063 < twelveMode.F 0
  mass : fourierMass twelveMode.F < 0.765870
  moment : logMoment twelveMode.F + 0.000002 < -1.37957
  variation : totalVariation twelveMode.F < 625
  log_variation : logVariation twelveMode.F < 2000

/-- The step heights indexed as in Lemma 20. -/
structure ShoulderSteps (e : ℕ → ℚ) : Prop where
  nonneg : ∀ j, 1 ≤ j → j ≤ 4001 → 0 ≤ e j
  antitone : ∀ j, 1 ≤ j → j ≤ 4000 → e (j + 1) ≤ e j
  last : e 4001 = 0
  first : e 1 < 0.76
  majorizes : ∀ j : ℕ, 1 ≤ j → j ≤ 4000 → ∀ s : ℝ,
    1 + ((j : ℝ) - 1) / 4000 < s → s ≤ 1 + (j : ℝ) / 4000 →
    twelveMode.positivePart s ≤ (e j : ℝ)

noncomputable def shoulderCharge (e : ℕ → ℚ) (b : ℕ → ℝ) (lo hi : ℝ) : ℝ :=
  8 * U₁ ^ 2 * ∑ j ∈ Finset.Icc 1 4000,
    let L := if 0 ≤ b j then hi else lo
    ((e j : ℝ) - (e (j + 1) : ℝ)) * ((j : ℝ) / 4000) * L / (L + b j)

noncomputable def bridgeComparison (k x : ℝ) : ℝ :=
  1.1 * k * x ^ ((1 : ℝ) / 10) * (x / (x + 1)) - 0.765870 * Real.log ((x + 1) / 1.1) + 1.37957

end Legendre
