import LeastPrime.Checker.CertificateData

/-! Executable partial certificates for the level-six lower bound. -/

namespace LeastPrime.Checker

def lowerSixStep : Nat := quotient .upper unit (bins .lower 6) - 1

def lowerSlicePassed (tail : Bool) (a b : Nat) : GridSet :=
  if tail then [(unit - b, unit - a), (a, b)] else [(a, b)]

def lowerSliceGap (tail : Bool) (a b : Nat) : GridInterval :=
  if tail then (unit - a, unit) else (b, unit - b)

def lowerSliceValue (tail : Bool) (a b left right : Nat) : Nat :=
  higherGap .lower lowerSixStep (probabilityBound .lower 5)
    (lowerSlicePassed tail a b) left right

/-- Check one additive level-six contribution, in square grid units. -/
def checkLowerSlice (tail : Bool) (a b left right expected : Nat) : Bool :=
  let gap := lowerSliceGap tail a b
  decide (0 < a ∧ a ≤ b ∧ b < unit - b ∧ gap.1 ≤ left ∧ left ≤ right ∧ right ≤ gap.2) &&
    (lowerSliceValue tail a b left right == expected)

/-- Add both target widths and the six unrounded gap contributions, then round once. -/
def lowerSliceRound (a b x₁ x₂ x₃ y₁ y₂ y₃ : Nat) : Nat :=
  quotient .lower (2 * (b - a) * unit + x₁ + x₂ + x₃ + y₁ + y₂ + y₃) unit

end LeastPrime.Checker
