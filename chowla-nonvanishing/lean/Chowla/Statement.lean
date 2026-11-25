import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace Chowla

open Filter
open scoped BigOperators

/-- Fundamental discriminants. The cutoff in `discs` excludes 1. -/
def IsFundDisc (d : ℤ) : Prop :=
  (d % 4 = 1 ∧ Squarefree d) ∨
  (d % 4 = 0 ∧ ((d / 4) % 4 = 2 ∨ (d / 4) % 4 = 3) ∧ Squarefree (d / 4))

/-- The local character at 2, lifted to the requested modulus. The signed odd part determines
whether the conductor-eight factor is the character of discriminant 8 or −8. -/
noncomputable def dyadicCharacter (d : ℤ) : DirichletCharacter ℂ d.natAbs :=
  if h8 : 8 ∣ d.natAbs then
    DirichletCharacter.changeLevel h8
      ((if (d / 8) % 4 = 1 then ZMod.χ₈ else ZMod.χ₈').ringHomComp (Int.castRingHom ℂ))
  else if h4 : 4 ∣ d.natAbs then
    DirichletCharacter.changeLevel h4 (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
  else 1

/-- The Kronecker character for a fundamental discriminant, in its local factorisation.
The odd factor at p is the Legendre character of the argument modulo p. -/
noncomputable def chi (d : ℤ) : DirichletCharacter ℂ d.natAbs :=
  dyadicCharacter d * ∏ p ∈ d.natAbs.primeFactors.erase 2,
    if hp : p.Prime ∧ p ∣ d.natAbs then
      letI : Fact p.Prime := ⟨hp.1⟩
      DirichletCharacter.changeLevel hp.2
        ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
    else 1

/-- The quadratic L-function at a nonzero modulus. The constant at modulus zero only
makes the function total on integers, which are the indices of the discriminant filters. -/
noncomputable def quadraticL (d : ℤ) (s : ℂ) : ℂ :=
  if hd : d.natAbs = 0 then 1
  else @DirichletCharacter.LFunction d.natAbs ⟨hd⟩ (chi d) s

theorem quadraticL_eq (d : ℤ) [NeZero d.natAbs] (s : ℂ) :
    quadraticL d s = DirichletCharacter.LFunction (chi d) s := by
  simp [quadraticL, NeZero.ne d.natAbs]

/-- The two signs and three conductor types of equation (1). -/
inductive DiscSign
  | positive | negative
  deriving DecidableEq, Fintype

inductive DiscType
  | odd | four | eight
  deriving DecidableEq, Fintype

abbrev DiscClass := DiscSign × DiscType

def DiscSign.value : DiscSign → ℤ
  | .positive => 1
  | .negative => -1

def DiscType.kappa : DiscType → ℕ
  | .odd => 1
  | .four => 4
  | .eight => 8

/-- Membership in one of the classes in equation (1), with a positive odd squarefree part. -/
def InClass (D : DiscClass) (d : ℤ) : Prop :=
  ∃ m : ℕ, Odd m ∧ Squarefree m ∧ d = (D.2.kappa : ℤ) * D.1.value * (m : ℤ) ∧
    match D.2 with
    | .odd => 1 < m ∧ (D.1.value * (m : ℤ)) % 4 = 1
    | .four => (D.1.value * (m : ℤ)) % 4 = 3
    | .eight => True

noncomputable def discs (X : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-⌊X⌋) ⌊X⌋).filter (fun d => IsFundDisc d ∧ 1 < |d|)

noncomputable def classDiscs (D : DiscClass) (X : ℝ) : Finset ℤ := by
  classical
  exact (discs X).filter (InClass D)

def CentralNonvanishing (d : ℤ) : Prop :=
  quadraticL d (1 / 2) ≠ 0

noncomputable def nonvanishing (ds : Finset ℤ) : Finset ℤ := by
  classical
  exact ds.filter CentralNonvanishing

/-- Theorem 1 for the union of the six classes. -/
def MainStatement : Prop :=
  ∃ c : ℝ, 0.9453419890 < c ∧ ∀ᶠ X in atTop,
    c * ((discs X).card : ℝ) ≤ ((nonvanishing (discs X)).card : ℝ)

/-- Theorem 1 in a single class of equation (1). -/
def ClassStatement (D : DiscClass) : Prop :=
  ∃ c : ℝ, 0.9453419890 < c ∧ ∀ᶠ X in atTop,
    c * ((classDiscs D X).card : ℝ) ≤ ((nonvanishing (classDiscs D X)).card : ℝ)

end Chowla
