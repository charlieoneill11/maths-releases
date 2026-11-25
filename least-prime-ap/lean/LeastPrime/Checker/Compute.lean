/-! Integer evaluation of the stick-breaking probability bounds. -/

namespace LeastPrime.Checker

abbrev GridInterval := Nat × Nat
abbrev GridSet := List GridInterval

def unit : Nat := 1000000

inductive Bound where
  | lower
  | upper
  deriving BEq, DecidableEq, Repr

def quotient (bound : Bound) (numerator denominator : Nat) : Nat :=
  match bound with
  | .lower => numerator / denominator
  | .upper => (numerator + (denominator - 1)) / denominator

def intervalLE (a b : GridInterval) : Bool :=
  decide (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2)

def mergeSorted (current : GridInterval) : List GridInterval → GridSet
  | [] => [current]
  | next :: rest =>
    if next.1 ≤ current.2 then
      mergeSorted (current.1, max current.2 next.2) rest
    else
      current :: mergeSorted next rest

def mergeIntervals (intervals : List GridInterval) : GridSet :=
  match intervals.mergeSort intervalLE with
  | [] => []
  | head :: tail => mergeSorted head tail

def reflectInterval (I : GridInterval) : GridInterval := (unit - I.2, unit - I.1)

def scaledInterval (bound : Bound) (a b : Nat) (I : GridInterval) : GridInterval :=
  match bound with
  | .lower => (quotient .upper (I.1 * unit) a, quotient .lower (I.2 * unit) b)
  | .upper => (quotient .lower (I.1 * unit) b, quotient .upper (I.2 * unit) a)

def keepInterval (bound : Bound) (I : GridInterval) : Bool :=
  match bound with
  | .lower => decide (I.1 < I.2)
  | .upper => decide (I.1 ≤ I.2)

def roundedIntervals (bound : Bound) (below : GridSet) (a b : Nat) : GridSet :=
  below.flatMap fun I =>
    let J := scaledInterval bound a b I
    if keepInterval bound J then [J, reflectInterval J] else []

def scaledTarget (bound : Bound) (below : GridSet) (a b : Nat) : GridSet :=
  mergeIntervals (roundedIntervals bound below a b)

def width (I : GridInterval) : Nat := I.2 - I.1

def targetLength (targets : GridSet) : Nat := (targets.map width).sum

def reflectedOverlap (r : Nat) (I J : GridInterval) : Nat :=
  min I.2 (r - J.1) - max I.1 (r - J.2)

def availableLength (bound : Bound) (below : GridSet) (r : Nat) : Nat :=
  match below with
  | [] => 0
  | head :: tail =>
    match bound with
    | .upper => max (r - ((head :: tail).getLastD head).1) head.2
    | .lower =>
      let overlap := (below.map fun I => (below.map (reflectedOverlap r I)).sum).sum
      2 * targetLength below - overlap

def breakpointCandidates (bound : Bound) (below : GridSet) : List Nat :=
  match below with
  | [] => []
  | head :: tail =>
    match bound with
    | .upper => [((head :: tail).getLastD head).1 + head.2]
    | .lower => below.flatMap fun I => below.flatMap fun J =>
      [I.1 + J.1, I.1 + J.2, I.2 + J.1, I.2 + J.2]

def gapCuts (bound : Bound) (below : GridSet) (a b : Nat) : List Nat :=
  (a :: b :: (breakpointCandidates bound below).filter (fun cut => a < cut && cut < b)).mergeSort

def midpoint (bound : Bound) (a b ga gb : Nat) : Nat :=
  quotient bound ((ga + gb) * unit) (a + b)

def trapezoid (bound : Bound) (a b ga gb : Nat) : Nat :=
  quotient bound (quotient bound (ga * unit) a + quotient bound (gb * unit) b) 2

def estimatedProbability (bound : Bound) (a b ga gb : Nat) : Nat :=
  let convex := decide (gb * a ≤ ga * b)
  if convex == (bound == .lower) then midpoint bound a b ga gb
  else trapezoid bound a b ga gb

def sumCutCells (bound : Bound) (g : Nat → Nat) (a ga : Nat) : List Nat → Nat
  | [] => 0
  | b :: rest =>
    let gb := g b
    (b - a) * estimatedProbability bound a b ga gb + sumCutCells bound g b gb rest

def finalGap (bound : Bound) (below : GridSet) (a b : Nat) : Nat :=
  if below.isEmpty || a == b then 0 else
    let g := availableLength bound below
    match gapCuts bound below a b with
    | [] => 0
    | start :: rest => sumCutCells bound g start (g start) rest

/-- Sum over gaps and target intervals from left to right. `below` stores the already passed
intervals in reverse order. -/
def integrateTarget (gap : GridSet → Nat → Nat → Nat) (below : GridSet) (previous : Nat) :
    List GridInterval → Nat
  | [] => gap below previous unit
  | I :: rest =>
    gap below previous I.1 + width I * unit + integrateTarget gap (I :: below) I.2 rest

/-- Sum on the prescribed grid of points spaced `step + 1` apart, clipping the last cell. -/
def sumGridCells (cell : Nat → Nat → Nat) (step a b : Nat) : Nat :=
  if _h : a < b then
    let right := min (a + (step + 1)) b
    cell a right + sumGridCells cell step right b
  else 0
termination_by b - a
decreasing_by simp_wf; omega

def higherGap (bound : Bound) (step : Nat) (recursive : GridSet → Nat)
    (below : GridSet) (a b : Nat) : Nat :=
  if below.isEmpty then 0 else
    sumGridCells (fun left right =>
      (right - left) * recursive (scaledTarget bound below left right)) step a b

def bins : Bound → Nat → Nat
  | .lower, 3 => 100
  | .lower, 4 => 220
  | .lower, 5 => 320
  | .lower, _ => 450
  | .upper, 3 => 400
  | .upper, 4 => 500
  | .upper, _ => 600

def probabilityBound (bound : Bound) (splits : Nat) (targets : GridSet) : Nat :=
  match targets with
  | [] => 0
  | head :: tail =>
    if head.1 = 0 then unit else
      match splits with
      | 0 => if bound == .lower then 0 else unit
      | 1 => if bound == .lower then targetLength targets else ((head :: tail).getLastD head).2
      | 2 => quotient bound (integrateTarget (finalGap bound) [] 0 targets) unit
      | k + 3 =>
        let step := quotient .upper unit (bins bound (k + 3)) - 1
        let gap := higherGap bound step (probabilityBound bound (k + 2))
        quotient bound (integrateTarget gap [] 0 targets) unit
termination_by structural splits

end LeastPrime.Checker

namespace LeastPrime

abbrev GridSet := Checker.GridSet

def lowerP (k : Nat) (T : GridSet) : Int := Checker.probabilityBound .lower k T

def upperQ (k : Nat) (T : GridSet) : Int := Checker.probabilityBound .upper k T

end LeastPrime
