import Chowla.SplineData
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Chowla.Checker

abbrev Primitive := ℕ → ℚ → ℚ

/-- A rational profile and all its lower primitives in the truncated-power basis. -/
def splinePrimitives (p : Spline) : Primitive :=
  fun n x => (p.primitive n).eval x

/-- The mean in Lemma 27. -/
def mean (B : Primitive) : ℚ := B 0 0 - (B 1 1 - B 1 0)

/-- The triangular integral in Lemma 27, as a second difference of the second primitive. -/
def triangle (B : Primitive) (t : ℚ) : ℚ :=
  B 2 (1 + t) - 2 * B 2 1 + B 2 (1 - t)

/-- The covariance in Lemma 27. The first term uses integration by parts once. -/
def covariance (B : Primitive) (t : ℚ) : ℚ :=
  4 * (t * B 1 t - B 2 t + B 2 0) - 2 * triangle B t

/-- Translations in Lemma 28 are recorded with their integral coefficients. -/
abbrev Shift := ℚ × ℤ

def Shift.translate (a : ℚ) (c : ℤ) (term : Shift) : Shift :=
  (term.1 + a, c * term.2)

private def collectShift (a : Shift) : List Shift → List Shift
  | [] => [a]
  | b :: bs =>
      if a.1 = b.1 then (a.1, a.2 + b.2) :: bs else a :: b :: bs

/-- Add adjacent coefficients at equal translation points. -/
def collectShifts (xs : List Shift) : List Shift :=
  xs.foldr collectShift []

/-- Multiply the discrete second-difference operator for one width into the accumulated shifts. -/
def extendShifts (a : ℚ) (xs : List Shift) : List Shift :=
  let left := xs.map (Shift.translate (-a) (-1))
  let middle := xs.map (Shift.translate 0 2)
  let right := xs.map (Shift.translate a (-1))
  let le := fun x y : Shift => decide (x.1 ≤ y.1)
  collectShifts (List.merge left (List.merge middle right le) le)

def shiftWeights (widths : List ℚ) : List Shift :=
  widths.foldr extendShifts [(0, 1)]

def shiftSum (shifts : List Shift) (f : ℚ → ℚ) (x : ℚ) : ℚ :=
  (shifts.map fun (s, weight) => (weight : ℚ) * f (x + s)).sum

theorem shiftSum_cons (a : Shift) (xs : List Shift) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (a :: xs) f x = (a.2 : ℚ) * f (x + a.1) + shiftSum xs f x := rfl

theorem shiftSum_append (xs ys : List Shift) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (xs ++ ys) f x = shiftSum xs f x + shiftSum ys f x := by
  simp [shiftSum]

private theorem shiftSum_collectShift (a : Shift) (ys : List Shift) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (collectShift a ys) f x = (a.2 : ℚ) * f (x + a.1) + shiftSum ys f x := by
  cases ys with
  | nil => rfl
  | cons b bs =>
    change shiftSum
      (if a.1 = b.1 then (a.1, a.2 + b.2) :: bs else a :: b :: bs) f x = _
    by_cases h : a.1 = b.1
    · rw [if_pos h]
      simp only [shiftSum_cons, Rat.intCast_add, h]
      ring
    · rw [if_neg h, shiftSum_cons]

theorem collectShifts_sound (xs : List Shift) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (collectShifts xs) f x = shiftSum xs f x := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change shiftSum (collectShift a (collectShifts as)) f x = _
    rw [shiftSum_collectShift, ih, shiftSum_cons]

private theorem shiftSum_translate (xs : List Shift) (a : ℚ) (c : ℤ) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (xs.map (Shift.translate a c)) f x = (c : ℚ) * shiftSum xs f (x + a) := by
  induction xs with
  | nil => simp [shiftSum]
  | cons t ts ih =>
    rw [List.map_cons, shiftSum_cons, ih, shiftSum_cons]
    simp only [Shift.translate, Rat.intCast_mul]
    rw [show x + (t.1 + a) = x + a + t.1 by ring]
    ring

theorem shiftSum_merge (xs ys : List Shift) (le : Shift → Shift → Bool) (f : ℚ → ℚ)
    (x : ℚ) : shiftSum (List.merge xs ys le) f x = shiftSum xs f x + shiftSum ys f x := by
  have h : (List.merge xs ys le).Perm (xs ++ ys) := List.merge_perm_append le
  rw [← shiftSum_append]
  exact (h.map (fun (t, weight) => (weight : ℚ) * f (x + t))).sum_eq

theorem extendShifts_sound (a : ℚ) (xs : List Shift) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (extendShifts a xs) f x =
      2 * shiftSum xs f x - shiftSum xs f (x + a) - shiftSum xs f (x - a) := by
  simp only [extendShifts, collectShifts_sound, shiftSum_merge, shiftSum_translate,
    add_zero, ← sub_eq_add_neg]
  norm_num
  ring

def shiftDifference (a : ℚ) (f : ℚ → ℚ) (x : ℚ) : ℚ :=
  2 * f x - f (x + a) - f (x - a)

/-- The compressed shift sum computes precisely the fold of the paper's translation operators. -/
theorem shiftWeights_sound (widths : List ℚ) (f : ℚ → ℚ) (x : ℚ) :
    shiftSum (shiftWeights widths) f x = (widths.foldr shiftDifference f) x := by
  induction widths generalizing x with
  | nil => simp [shiftWeights, shiftSum]
  | cons a as ih =>
    change shiftSum (extendShifts a (shiftWeights as)) f x = _
    rw [extendShifts_sound, ih, ih, ih]
    rfl

/-- The signed lower primitive from Lemma 28. The polynomial correction is evaluated by Horner's
rule, with the values of lower primitives at zero shared across all shift evaluations. -/
def oddPrimitiveCoefficients (B : Primitive) (n : ℕ) : List ℚ :=
  (List.range n).map fun k => B (n - k) 0 / k.factorial

def evaluateOddPrimitive (B : ℚ → ℚ) (coefficients : List ℚ) (x : ℚ) : ℚ :=
  if x < 0 then -B x
  else B x - 2 * (coefficients.foldr (fun c rest => c + x * rest) 0)

def oddPrimitive (B : Primitive) (n : ℕ) : ℚ → ℚ :=
  evaluateOddPrimitive (B n) (oddPrimitiveCoefficients B n)

def cumulantFactor (n : ℕ) : ℚ := (-2 : ℚ) ^ n / 2

/-- Restricted cumulant with a distinguished spline profile and zero or more rectangle profiles. -/
def markedCumulant (B : Primitive) (widths : List ℚ) : ℚ :=
  match widths with
  | [] => mean B
  | [t] => covariance B t
  | a :: b :: rest =>
      let widths := a :: b :: rest
      let n := widths.length + 1
      let coefficients := oddPrimitiveCoefficients B n
      cumulantFactor n *
        shiftSum (shiftWeights widths) (evaluateOddPrimitive (B n) coefficients) 1

/-- Exact coefficient of the tail for rectangle profiles alone. The signed rectangle at width
`a` is the sum of step functions at `-a, 0, a` with coefficients `-1, 2, -1`. Their convolution
and lower primitive give a normalized truncated power of degree `widths.length`. -/
def rectangleTail (widths : List ℚ) : ℚ :=
  if widths.length < 2 || widths.sum ≤ 1 then 0
  else
    let n := widths.length
    cumulantFactor n *
      shiftSum (shiftWeights widths) (fun x => (max x 0) ^ n / n.factorial) 1

/-- Ascending rational coefficients for the positive half of the Taylor profile. -/
def hstarCoefficients : Spline.Coefficients :=
  let A : ℚ := 61453967058074 / (10 : ℚ)^14
  (List.range 13).map fun k =>
    (if k % 2 = 0 then A else 1/4 - A) * (-1 : ℚ) ^ (k / 2) / (2 ^ k * k.factorial)

/-- The half-open spline representation of the Taylor polynomial in Lemma 29. -/
def hstarSpline : Spline :=
  Spline.piece (hstarCoefficients.scaleInput (-1)) (-1) 0 ++
    Spline.piece hstarCoefficients 0 1

/-- The enclosure error from Lemma 30 before applying the row's external weight. -/
def centralError (widths coefficients : List ℚ) : ℚ :=
  let s := 1 - widths.sum
  let weight := (coefficients.map fun c => max c (-c)).sum
  match widths with
  | [] => 0
  | [a] => 8 * a ^ 2 * s * weight / (10 : ℚ) ^ 12
  | _ =>
      (2 : ℚ) ^ widths.length * (2 / (10 : ℚ) ^ 12) * (2 * s * weight) *
        (widths.map (fun a => 2 * a)).prod

structure CentralBounds where
  lower : ℚ
  upper : ℚ
  deriving Repr

/-- Evaluate the contribution of a row with its unweighted rational profile already prepared. -/
def centralFromSpline (widths coefficients : List ℚ) (weight : ℚ) (p : Spline) :
    CentralBounds :=
  if widths.isEmpty then ⟨0, 0⟩
  else
    let value := weight * markedCumulant (splinePrimitives (hstarSpline.convolution p)) widths
    let error := max weight (-weight) * centralError widths coefficients
    ⟨value - error, value + error⟩

end Chowla.Checker
