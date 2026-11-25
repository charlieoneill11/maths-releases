import Chowla.Certificate
import Chowla.Cited
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-- The GRH proposition from the original RH project's `src/Statements.lean`. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

namespace Chowla

open Filter
open scoped BigOperators SchwartzMap Topology

/-- The fixed weight of §2.2, extended by zero outside its support. -/
structure ShellWeight where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) toFun
  compact : HasCompactSupport toFun
  supported : tsupport toFun ⊆ Set.Ioo 1 2
  nonnegative : ∀ x, 0 ≤ toFun x
  nonzero : toFun ≠ 0

/-- The real even Schwartz tests of Theorem 7. Their Fourier transforms are smooth by Schwartz
Fourier theory, and this structure requires compact Fourier support. -/
structure MomentTest where
  toSchwartz : 𝓢(ℝ, ℝ)
  even : Function.Even (fun x => toSchwartz x)
  compactFourier : HasCompactSupport (fourier (fun x => toSchwartz x))

noncomputable def MomentTest.profile (f : MomentTest) : ℝ → ℝ :=
  fun u => (fourier (fun x => f.toSchwartz x) u).re

noncomputable def oddPart (D : DiscClass) (d : ℤ) : ℝ :=
  (d.natAbs : ℝ) / (D.2.kappa : ℝ)

noncomputable def weightedSum (D : DiscClass) (W : ShellWeight) (X : ℝ) (φ : ℤ → ℝ) : ℝ :=
  ∑ d ∈ classDiscs D (2 * (D.2.kappa : ℝ) * X), W.toFun (oddPart D d / X) * φ d

noncomputable def weightedAverage (D : DiscClass) (W : ShellWeight) (X : ℝ) (φ : ℤ → ℝ) : ℝ :=
  weightedSum D W X φ / weightedSum D W X (fun _ => 1)

/-- The summands of the zero statistic in §2.3. -/
noncomputable def zeroSummand (f : ℝ → ℝ) (d : ℤ) (X : ℝ) (z : ZeroCopy d) : ℝ :=
  f (z.ordinate * Real.log X / (2 * Real.pi))

/-- The linear zero statistic. Its series is to be shown summable for the Schwartz tests,
using the zero count in `CitedFacts`. -/
noncomputable def zeroStatistic (f : ℝ → ℝ) (d : ℤ) (X : ℝ) : ℝ :=
  ∑' z : ZeroCopy d, zeroSummand f d X z

structure PaperClaims : Prop where
  /-- Theorem 7 of this paper, for the empty pattern in each class. Its proof is in §3,
  uses GRH and is outside the formalisation. -/
  emptyPatternMoments :
    ∀ (D : DiscClass) (W : ShellWeight) (k : ℕ) (_ : 0 < k) (f : Fin k → MomentTest),
      (∑ i, radius (f i).profile) < 2 →
      Tendsto
        (fun X : ℝ => weightedAverage D W X
          (fun d => ∏ i, zeroStatistic (fun x => (f i).toSchwartz x) d X))
        atTop (𝓝 (modelMoment fun i => (f i).profile))

end Chowla
