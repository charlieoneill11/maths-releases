import HadwigerNelson.Certificate.Hole.Runtime

/-! The short-edge and unit-edge credit quadratures used for W_V. The common
integer denominator represents overlap areas exactly. Only products by the
half-angle bin lengths require additional outward rounding. -/
namespace HadwigerNelson.Certificate.Hole

def denom : ℤ := 2 * (PartialWave.scale : ℤ) * PartialWave.xInt
def radiusR : ℚ := 53/20000
def radiusD : ℚ := 1837/500000
def unitWidth : ℚ := (73/10000)/16384
def unitT (i : ℕ) : ℚ := i*unitWidth

def tickArea (x y : ℚ) : ℤ :=
  ticks (x*PartialWave.scale).ceil (y*PartialWave.scale).ceil

def unitAt (i : ℕ) : ℤ := tickArea (unitT i) (unitT i ^ 2/2)

def unitRows (n : Nat) : Array ℤ :=
  (Array.range n).foldl (fun a i => a.push (min (a[i]?.getD 0) (unitAt (i+1)))) #[denom]

theorem unitRows_zero : unitRows 0 = #[denom] := rfl

theorem unitRows_succ (n : ℕ) : unitRows (n+1) =
    (unitRows n).push (min ((unitRows n)[n]?.getD 0) (unitAt (n+1))) := by
  unfold unitRows
  rw [Array.range_succ,Array.append_singleton,Array.foldl_push]

def shortAt (r : ℚ) (i : ℕ) : ℤ :=
  let l : ℚ := i/8192
  let u : ℚ := (i+1:ℕ)/8192
  tickArea (2*r*(1-l^2)/(1+l^2)) (4*r*u/(1+u^2))

def shortWeight (i : ℕ) : ℚ :=
  let u : ℚ := (i+1:ℕ)/8192
  (2/8192)/(1+u^2)

/-- Round downward after each weighted term to keep denominators bounded. -/
def weightScale : ℤ := 10^32
def weightedTicks (h : ℚ) (i : ℕ) : ℤ :=
  (h*shortWeight i*weightScale).floor

def shortRows (r : ℚ) : Array ℤ := Array.ofFn fun i : Fin 8192 => shortAt r i.val

def shortMax (a : Array ℤ) : ℤ := a.foldl max 0

def shortCap (a : Array ℤ) (f : ℚ) : ℚ := f*shortMax a/denom

def shortSum (a : Array ℤ) (cap : ℚ) : ℤ :=
  (Array.ofFn (fun i : Fin 8192 =>
    weightedTicks (min ((a[i.val]?.getD 0 : ℚ)/denom) cap) i.val)).sum

def clippedMean (a : Array ℤ) (cap : ℚ) : ℚ :=
  (2/(355/113)) * (shortSum a cap : ℚ) / weightScale

def unitSum (rows : Array ℤ) : ℤ :=
  (Array.ofFn (fun i : Fin 16384 => rows[i.val+1]?.getD 0)).sum

def retainedSum (rows : Array ℤ) (cap : ℚ) : ℚ :=
  (Array.ofFn (fun i : Fin 16384 => max ((rows[i.val+1]?.getD 0 : ℚ)/denom - cap) 0)).sum

def checkMeans : Bool :=
  let units := unitRows 16384
  let unitTotal := (unitSum units : ℚ)/denom
  let r := shortRows radiusR
  let d := shortRows radiusD
  let rCap := shortCap r (3/4)
  let dCap := shortCap d (3/10)
  decide (112668096940/10^18 ≤ 2*unitWidth/(355/113)*unitTotal ∧
    16034576942481/10^18 ≤ clippedMean r rCap ∧
    3057937052494/10^18 ≤ clippedMean d dCap ∧
    0 < unitTotal ∧ 344/1000*unitTotal ≤ retainedSum units rCap ∧
    761/1000*unitTotal ≤ retainedSum units dCap)

end HadwigerNelson.Certificate.Hole
