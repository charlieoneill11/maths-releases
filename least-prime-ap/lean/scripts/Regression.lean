import LeastPrime.Checker.Compute

open LeastPrime.Checker

private def intervalsFromEndpoints : List Nat → Option GridSet
  | [] => some []
  | low :: high :: rest => (intervalsFromEndpoints rest).map ((low, high) :: ·)
  | [_] => none

def main : IO Unit := do
  let input ← IO.getStdin
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let words := line.trimAscii.toString.splitOn " "
    let some (side :: level :: endpoints) := words.mapM String.toNat?
      | throw (IO.userError "Expected side, level and endpoint pairs")
    let some intervals := intervalsFromEndpoints endpoints
      | throw (IO.userError "Expected paired endpoints")
    let bound := if side = 0 then Bound.lower else Bound.upper
    IO.println (probabilityBound bound level intervals)
