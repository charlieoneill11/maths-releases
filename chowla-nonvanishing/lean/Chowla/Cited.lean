import Chowla.Statement
import Mathlib.Analysis.Analytic.Order

namespace Chowla

/-- One index for each zero in the critical strip, with a copy for every unit of multiplicity.
The imaginary part, after GRH, gives its ordinate in §2.3. -/
def ZeroCopy (d : ℤ) :=
  Σ s : {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ quadraticL d s = 0},
    {n : ℕ // (n : ℕ∞) < analyticOrderAt (quadraticL d) s.val}

def ZeroCopy.ordinate {d : ℤ} (z : ZeroCopy d) : ℝ := z.1.val.im

def zerosInBand (d : ℤ) (T : ℝ) : Set (ZeroCopy d) :=
  {z | T ≤ |z.ordinate| ∧ |z.ordinate| ≤ T + 1}

/-- Mathlib's completed function includes the gamma factor. Insert the conductor factor for the
functional equation in Lemma 4. The convention differs only by a constant independent of s. -/
noncomputable def completed (d : ℤ) (s : ℂ) : ℂ :=
  if hd : d.natAbs = 0 then 1
  else (d.natAbs : ℂ) ^ (s / 2) *
    @DirichletCharacter.completedLFunction d.natAbs ⟨hd⟩ (chi d) s

structure CitedFacts : Prop where
  /-- Davenport, *Multiplicative Number Theory*, chapters 2, 6 and 9.
  The quadratic Gauss sum makes the root number +1 in the completed functional equation. -/
  rootNumberOne : ∀ d : ℤ, IsFundDisc d → 1 < |d| → ∀ s : ℂ, completed d s = completed d (1 - s)
  /-- Davenport, *Multiplicative Number Theory*, chapter 16.
  Unit intervals in absolute ordinate contain at most a constant times `log(|d|(T+2))`
  zeros with multiplicity. -/
  zeroCount : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℤ), IsFundDisc d → 1 < |d| → ∀ T : ℝ, 0 ≤ T →
    (zerosInBand d T).Finite ∧
      ((zerosInBand d T).ncard : ℝ) ≤ C * Real.log ((d.natAbs : ℝ) * (T + 2))

end Chowla
