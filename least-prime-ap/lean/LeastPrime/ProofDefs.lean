import LeastPrime.Statement

/-! Definitions shared by the probabilistic and arithmetic proofs. -/

namespace LeastPrime

open MeasureTheory Set

noncomputable section

/-- Reflection about the midpoint of the unit interval. -/
def reflect (T : Set ℝ) : Set ℝ := (fun t : ℝ => 1 - t) '' T

def IsSymmetric (T : Set ℝ) : Prop := T = reflect T

def intervalUnion (intervals : List (ℝ × ℝ)) : Set ℝ :=
  ⋃ I ∈ intervals, Icc I.1 I.2

def IsClosedTarget (T : Set ℝ) : Prop :=
  ∃ intervals : List (ℝ × ℝ),
    (∀ I ∈ intervals, 0 ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ 1) ∧ T = intervalUnion intervals

def HasInteriorEndpoints (T : Set ℝ) : Prop :=
  ∃ intervals : List (ℝ × ℝ),
    (∀ I ∈ intervals, 0 < I.1 ∧ I.1 ≤ I.2 ∧ I.2 < 1) ∧ T = intervalUnion intervals

def p (j : ℕ) (T : Set ℝ) : ℝ := (stickLaw j).real (E j T)
def q (j : ℕ) (T : Set ℝ) : ℝ := (stickLaw j).real (F j T)

def rescale (r : ℝ) (T : Set ℝ) : Set ℝ := (fun t : ℝ => t / r) '' (T ∩ Icc 0 r)

def residualTarget (r : ℝ) (T : Set ℝ) : Set ℝ := rescale r T ∪ reflect (rescale r T)

def gLower (r : ℝ) (W : Set ℝ) : ℝ := volume.real (W ∪ (fun w : ℝ => r - w) '' W)

open Classical in
def gUpper (r : ℝ) (W : Set ℝ) : ℝ :=
  if W.Nonempty then max (r - sInf W) (sSup W) else 0

def cellInner (a b : ℝ) (intervals : List (ℝ × ℝ)) : Set ℝ :=
  intervalUnion (intervals.map fun (l, u) => (l / a, u / b))

def cellOuter (a b : ℝ) (intervals : List (ℝ × ℝ)) : Set ℝ :=
  intervalUnion (intervals.map fun (l, u) => (l / b, u / a))

def HasLogDivisorIn (n : ℕ) (T : Set ℝ) : Prop :=
  ∃ d ∈ n.divisors, Real.log (d : ℝ) / Real.log (n : ℝ) ∈ T

def windowCount (Q : ℝ) (P : ℕ → Prop) : ℕ := by
  classical
  exact ((window Q).filter P).card

def revealedVector (j n : ℕ) (factors : List ℕ) : Fin j → ℝ :=
  fun i => Real.log ((factors[i.val]?.getD 1 : ℕ) : ℝ) / Real.log (n : ℝ)

end

end LeastPrime
