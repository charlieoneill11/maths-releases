import Chowla.CheckerGrid
import Chowla.Stages

namespace Chowla.Checker

/-- Preserve the published program's rounding groups by splitting the
deterministic R0 row at its seventh coefficient. -/
def splitStageOneRow (r : Rows.RowData) : Rows.RowData × Rows.RowData :=
  ({ r with coefficients := r.coefficients.take 7 },
   { r with coefficients := List.replicate 7 0 ++ r.coefficients.drop 7 })

def stageOneLinear : List Rows.RowData :=
  (Rows.r0.map fun r => (splitStageOneRow r).1) ++ Rows.r1Grid ++
    (Rows.r0.map fun r => (splitStageOneRow r).2) ++ Rows.r1Modes

def stageOneQuadratic : List Rows.RowData := Rows.r2

def stageOneCentral (_ : Unit) : CentralBounds :=
  let center := GridSpline.pack hstarSpline
  (stageOneLinear ++ stageOneQuadratic).foldl (fun acc r =>
    let c := centralGrid center (prepareGrid r)
    ⟨acc.lower + c.lower, acc.upper + c.upper⟩) ⟨0, 0⟩

/-- Ceiling after expressing a value in units of 10⁻⁸. -/
def roundUpStageOne (q : ℚ) : ℤ :=
  let scaled := q * 100000000
  Int.neg (Int.neg scaled.num / (scaled.den : ℤ))

def normRow (rows : Array GridRow) (i : ℕ) (r : GridRow) : ℚ := Id.run do
  let mut total := 0
  for j in [:min (i + 1) rows.size] do
    if let some c := rows[j]? then
      total := total + (if j = i then 1 else 2) * gramGrid r c
  return total

def crossRow (r : GridRow) (rows : Array GridRow) : ℚ :=
  2 * (rows.foldl (fun total c => total + gramGrid r c) 0)

def roundedLinearBlock (linear quadratic : Array GridRow) (start stop : ℕ) : ℤ := Id.run do
  let mut total := 0
  for i in [start : min stop linear.size] do
    if let some r := linear[i]? then
      total := total + roundUpStageOne (normRow linear i r + crossRow r quadratic)
  return total

def roundedQuadraticBlock (rows : Array GridRow) (start stop : ℕ) : ℤ := Id.run do
  let mut total := 0
  for i in [start : min stop rows.size] do
    if let some r := rows[i]? then
      total := total + roundUpStageOne (normRow rows i r)
  return total

def stageOneUpperGram (_ : Unit) : ℚ :=
  let linear := stageOneLinear.toArray.map prepareGrid
  let quadratic := stageOneQuadratic.toArray.map prepareGrid
  let sum := roundedLinearBlock linear quadratic 0 linear.size +
    roundedQuadraticBlock quadratic 0 quadratic.size
  (sum : ℚ) / 100000000

def stageOneBounds (_ : Unit) : StageBounds :=
  let center := stageOneCentral ()
  ⟨center.lower, center.upper, stageOneUpperGram (), 0⟩

def addCentralBounds (x y : CentralBounds) : CentralBounds :=
  ⟨x.lower + y.lower, x.upper + y.upper⟩

def centralRows (rows : Array GridRow) : CentralBounds :=
  let center := GridSpline.pack hstarSpline
  rows.foldl (fun acc r => addCentralBounds acc (centralGrid center r)) ⟨0, 0⟩

/-- Evaluate the increase in the Gram square from appending a finite array of rows. -/
def gramIncrease (old new : Array GridRow) : ℚ := Id.run do
  let mut total := 0
  for i in [:new.size] do
    if let some row := new[i]? then
      total := total + crossRow row old + normRow new i row
  return total

def earlyBounds (i : Fin 8) (previous : StageBounds) (old new : Array GridRow) : StageBounds :=
  let c := addCentralBounds ⟨previous.lowerCentral, previous.upperCentral⟩ (centralRows new)
  let g := stageProportion i - p₀
  let d := previous.upperCentral ^ 2 / (2 * g) + gramIncrease old new
  ⟨c.lower, c.upper, d, 0⟩

def scaleGridRow (r : GridRow) (z : ℚ) : GridRow :=
  { r with row := { r.row with weight := z * r.row.weight } }

def prepareRows (rows : List Rows.RowData) : Array GridRow := rows.toArray.map prepareGrid

def firstFourRows (stage : ℕ) : List Rows.RowData :=
  stageOneLinear ++ stageOneQuadratic ++
    (if 2 ≤ stage then Rows.r3 else []) ++
    (if 3 ≤ stage then Rows.r4 else []) ++
    (if 4 ≤ stage then Rows.r5 else [])

def lateInherited (stage : ℕ) : Array GridRow :=
  let old := (prepareRows (firstFourRows 4)).map (scaleGridRow · Rows.inheritedWeight)
  old ++ prepareRows (Rows.r6 ++ (if 7 ≤ stage then Rows.r7 else []) ++
    (if 8 ≤ stage then Rows.r8 else []))

def lateBounds (base : ℚ) (stage : ℕ) (newRows : List Rows.RowData) : StageBounds :=
  let new := prepareRows newRows
  let p := base + (centralRows new).lower - gramIncrease (lateInherited stage) new / 2
  ⟨0, 0, 0, p⟩

/-- Compute a single stage from the preceding reported bounds. Stages one and six
use the start values specified in the paper. The remaining stages reuse the preceding
enclosures and never recompute the earlier Gram square. -/
def evaluateStage (i : Fin 8) (previous : StageBounds) : StageBounds :=
  match i.val with
  | 0 => stageOneBounds ()
  | 1 => earlyBounds 0 previous (prepareRows (firstFourRows 1)) (prepareRows Rows.r3)
  | 2 => earlyBounds 1 previous (prepareRows (firstFourRows 2)) (prepareRows Rows.r4)
  | 3 => earlyBounds 2 previous (prepareRows (firstFourRows 3)) (prepareRows Rows.r5)
  | 4 =>
    let z := Rows.inheritedWeight
    let inherited := (prepareRows (firstFourRows 4)).map (scaleGridRow · z)
    let new := prepareRows Rows.r6
    let d := previous.upperCentral ^ 2 / (2 * (stageProportion 3 - p₀))
    let p := p₀ + z * previous.lowerCentral + (centralRows new).lower -
      (z ^ 2 * d + gramIncrease inherited new) / 2
    ⟨0, 0, 0, p⟩
  | 5 => lateBounds (stageProportion 4) 6 Rows.r7
  | 6 => lateBounds previous.lowerProportion 7 Rows.r8
  | _ => lateBounds previous.lowerProportion 8 Rows.r9

/-- Replay all eight calculations explicitly, in stage order. -/
def evaluateStages (_ : Unit) : Array StageBounds := Id.run do
  let mut previous := ⟨0, 0, 0, 0⟩
  let mut stages := #[]
  for i in List.finRange 8 do
    previous := evaluateStage i previous
    stages := stages.push previous
  return stages

theorem roundUpStageOne_sound (q : ℚ) :
    q ≤ (roundUpStageOne q : ℚ) / 100000000 := by
  rw [le_div_iff₀ (by norm_num)]
  simpa [roundUpStageOne, Rat.ceil_def'] using Int.le_ceil (q * 100000000)

end Chowla.Checker
