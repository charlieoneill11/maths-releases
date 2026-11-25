import Chowla.CheckerStages

open Chowla Chowla.Checker

private def showRat (q : ℚ) : String := s!"{q.num}/{q.den}"

private def parseIndex (input : String) : IO ℕ := do
  let some index := input.toNat? | throw (IO.userError ("Invalid index " ++ input))
  return index

private def getRow (data : Array (Array GridRow)) (group index : String) : IO GridRow := do
  let groupIndex ← parseIndex group
  let rowIndex ← parseIndex index
  let some row := (data[groupIndex]?).bind (fun rows => rows[rowIndex]?) |
    throw (IO.userError s!"Row {index} in group {group} out of range")
  return row

/-- Read exact-value queries and emit their rational answers. This command introduces no theorem.
Group 10 is the stage-one linear list in the released order, including the split deterministic row. -/
def main (args : List String) : IO Unit := do
  let some file := args.head? | throw (IO.userError "Expected a file of exact-value queries")
  let data := #[
    Rows.r0, Rows.r1Grid ++ Rows.r1Modes, Rows.r2, Rows.r3, Rows.r4,
    Rows.r5, Rows.r6, Rows.r7, Rows.r8, Rows.r9, stageOneLinear
  ].map (fun rows => rows.toArray.map prepareGrid)
  let center := GridSpline.pack hstarSpline
  for line in ← IO.FS.lines file do
    match line.splitOn " " with
    | [a, i, b, j] =>
      let left ← getRow data a i
      let right ← getRow data b j
      IO.println (showRat (gramGrid left right))
    | ["C", a, i] =>
      let row ← getRow data a i
      let bound := centralGrid center row
      IO.println (showRat bound.lower ++ " " ++ showRat bound.upper)
    | _ => throw (IO.userError ("Invalid exact-value query " ++ line))
