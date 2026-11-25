import Chowla.LinearSource
import Chowla.Rows

namespace Chowla

/-- Round a fraction with positive denominator to the nearest integer, with ties to even.
The Euclidean quotient gives the lower integer also for negative numerators. -/
def roundHalfEven (num den : ℤ) : ℤ :=
  let q := num / den
  let twiceRem := 2 * (num % den)
  if twiceRem < den then q
  else if den < twiceRem then q + 1
  else if q % 2 = 0 then q else q + 1

private def sourceCoefficient (i j : ℕ) : ℤ :=
  if 1 ≤ i ∧ i ≤ 159 then ((Rows.linearSource[i - 1]?.getD #[])[j]?).getD 0
  else 0

private def spreadIncrement (i j k : ℕ) : ℤ :=
  if i = 0 ∨ 160 ≤ i then 0
  else
    let twiceSmooth := if i % 8 = 0 then sourceCoefficient (i - 1) j + sourceCoefficient (i + 1) j
      else 2 * sourceCoefficient i j
    roundHalfEven (twiceSmooth * (4 - (k : ℤ))) 32

/-- The coefficient of column j at fine-grid point l in §8.1. At a centre there are
three symmetric decrements. Between centres, only the two adjacent centres contribute. -/
def spreadCoefficient (l j : ℕ) : ℤ :=
  let i := l / 4
  let k := l % 4
  if k = 0 then sourceCoefficient i j - 2 *
    (spreadIncrement i j 1 + spreadIncrement i j 2 + spreadIncrement i j 3)
  else spreadIncrement i j k + spreadIncrement (i + 1) j (4 - k)

def spreadRow (l : ℕ) : Rows.RowData :=
  ⟨[(l : ℚ) / 640], (List.range 7).map (fun j => (spreadCoefficient l j : ℚ)), 1⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Independently check all fine-grid coefficients against the importer output. -/
theorem r1Grid_agrees : Rows.r1Grid = (List.range 639).map (fun i => spreadRow (i + 1)) := by
  decide +kernel

end Chowla
