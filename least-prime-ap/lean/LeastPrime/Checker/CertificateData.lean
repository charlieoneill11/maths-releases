import LeastPrime.Checker.Compute

/-! Boolean checks for the published symmetric grid windows. -/

namespace LeastPrime.Checker

def symmetricWindow (a b : Nat) : GridSet := [(a, b), (unit - b, unit - a)]

/-- Check the window's endpoint conditions and the verifier's exact integer output. -/
def checkWindow (bound : Bound) (k a b expected : Nat) : Bool :=
  decide (a ≤ b ∧ b < unit - b) && (probabilityBound bound k (symmetricWindow a b) == expected)

end LeastPrime.Checker
