import Chowla.CheckerMatching

namespace Chowla.Checker

/-- All cutoffs, convolution knots, and evaluation points in the certificate
use this common grid. -/
def grid : ℕ := 640

/-- Ascending normalized truncated-power coefficients at one knot. -/
structure GridJet where
  knot : ℤ
  coefficients : Array ℤ

/-- Coefficients carry one common denominator after replacing x by x / grid. -/
structure GridSpline where
  denominator : ℕ
  degree : ℕ
  jets : List GridJet

def addArrays (a b : Array ℤ) : Array ℤ :=
  (List.range (max a.size b.size)).toArray.map fun i => a[i]?.getD 0 + b[i]?.getD 0

def addJet (a : GridJet) : List GridJet → List GridJet
  | [] => [a]
  | b :: bs =>
    if a.knot = b.knot then
      { b with coefficients := addArrays a.coefficients b.coefficients } :: bs
    else b :: addJet a bs

def singleCoefficient (degree : ℕ) (coefficient : ℤ) : Array ℤ :=
  (Array.replicate degree 0).push coefficient

/-- Pack a rational spline when its knots lie on the certificate grid. -/
def GridSpline.pack (p : Spline) : Option GridSpline := do
  if !p.all (fun t => ((grid : ℚ) * t.knot).den == 1) then none
  else
    let scaled := p.map fun t =>
      (((grid : ℚ) * t.knot).num, t.degree, t.coefficient / (grid : ℚ) ^ t.degree)
    let D := scaled.foldl (fun acc (_, _, c) => acc.lcm c.den) 1
    let degree := scaled.foldl (fun acc (_, j, _) => max acc j) 0
    let jets := scaled.foldl (fun acc (k, j, c) =>
      if c = 0 then acc else
        addJet ⟨k, singleCoefficient j (c.num * (D / c.den : ℕ))⟩ acc) []
    some ⟨D, degree, jets⟩

/-- The extra integration in the convolution of two normalized basis elements
adds one degree and one grid factor to the denominator. -/
def convolveCoefficients (a b : Array ℤ) : Array ℤ := Id.run do
  let mut coefficients := Array.replicate (a.size + b.size) (0 : ℤ)
  for i in [:a.size] do
    let x := a[i]?.getD 0
    for j in [:b.size] do
      let y := b[j]?.getD 0
      coefficients := coefficients.modify (i + j + 1) (· + x * y)
  return coefficients

def GridSpline.convolution (p q : GridSpline) : GridSpline :=
  let jets := p.jets.foldl (fun acc a =>
    q.jets.foldl (fun acc b =>
      addJet ⟨a.knot + b.knot, convolveCoefficients a.coefficients b.coefficients⟩ acc)
      acc) []
  ⟨p.denominator * q.denominator * grid, p.degree + q.degree + 1, jets⟩

private def factorialTable : Array ℕ := (List.range 128).toArray.map Nat.factorial

/-- Most primitive factorials share the same small indices throughout the certificate. -/
def cachedFactorial (n : ℕ) : ℕ :=
  match factorialTable[n]? with
  | some v => v
  | none => n.factorial

theorem cachedFactorial_eq (n : ℕ) : cachedFactorial n = n.factorial := by
  by_cases h : n < 128
  · have hsize : n < factorialTable.size := by
      simpa [factorialTable] using h
    rw [cachedFactorial, Array.getElem?_eq_getElem hsize]
    simp [factorialTable]
  · have hsize : factorialTable.size ≤ n := by
      simpa [factorialTable] using (Nat.le_of_not_gt h)
    rw [cachedFactorial, Array.getElem?_eq_none hsize]

/-- Data shared by every evaluation at one primitive order. -/
structure GridPrimitive where
  denominator : ℕ
  order : ℕ
  jets : List GridJet

/-- Pre-scale all factorial denominators for a fixed primitive order. -/
def GridSpline.primitive (p : GridSpline) (n : ℕ) : GridPrimitive :=
  let factorial := cachedFactorial (p.degree + n)
  let denominator := p.denominator * grid ^ n * factorial
  let jets := p.jets.map fun jet =>
    let coefficients := jet.coefficients.mapIdx fun j (c : ℤ) =>
      c * (factorial / cachedFactorial (j + n) : ℕ)
    ⟨jet.knot, coefficients⟩
  ⟨denominator, n, jets⟩

/-- Evaluate the pre-scaled polynomial at integer grid coordinates by Horner's rule. -/
def GridPrimitive.eval (p : GridPrimitive) (x : ℤ) : ℚ :=
  let numerator := p.jets.foldl (fun acc jet =>
    let y := x - jet.knot
    if y < 0 then acc
    else
      let poly := jet.coefficients.foldr (fun c rest => c + y * rest) (0 : ℤ)
      acc + poly * y ^ p.order) 0
  (numerator : ℚ) / (p.denominator : ℚ)

def GridSpline.cache (p : GridSpline) (maxOrder : ℕ) : Array GridPrimitive :=
  (List.range (maxOrder + 1)).toArray.map p.primitive

def gridPrimitives (cache : Array GridPrimitive) (fallback : Primitive) : Primitive :=
  fun n x =>
    let X := (grid : ℚ) * x
    match cache[n]? with
    | some evaluator => if X.den = 1 then evaluator.eval X.num else fallback n x
    | none => fallback n x

structure GridRow where
  row : PreparedRow
  packed : Option GridSpline

def prepareGrid (row : Rows.RowData) : GridRow :=
  let row := prepare row
  ⟨row, GridSpline.pack row.profile⟩

/-- Use integers during the primitive evaluation of a Gram entry. The exact
rational evaluator also handles inputs outside the fixed grid. -/
def gramGrid (left right : GridRow) : ℚ :=
  let p := left.row
  let q := right.row
  match left.packed, right.packed with
  | some P, some Q =>
    let fallback := fun n x => splinePrimitives (p.profile.convolution q.profile) n x
    let cache := (P.convolution Q).cache (p.widths.length + q.widths.length + 1)
    p.weight * q.weight * contraction (gridPrimitives cache fallback) p.widths q.widths
  | _, _ => gram p q

/-- The rational Taylor-product enclosure using integer-grid primitives. -/
def centralGrid (center : Option GridSpline) (r : GridRow) : CentralBounds :=
  let row := r.row
  if row.widths.isEmpty then ⟨0, 0⟩
  else
    match center, r.packed with
    | some P, some Q =>
      let fallback := fun n x =>
        splinePrimitives (hstarSpline.convolution row.profile) n x
      let cache := (P.convolution Q).cache (row.widths.length + 1)
      let value := row.weight * markedCumulant (gridPrimitives cache fallback) row.widths
      let error := max row.weight (-row.weight) * centralError row.widths row.coefficients
      ⟨value - error, value + error⟩
    | _, _ => central row

end Chowla.Checker
