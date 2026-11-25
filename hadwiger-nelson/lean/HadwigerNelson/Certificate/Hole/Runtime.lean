import HadwigerNelson.Data.PartialWave
import HadwigerNelson.Arithmetic.Basic
import Mathlib.Data.Rat.Floor

/-! Lower overlap for the fixed W_V profile, in the integer units of Definition 18.
Its two interleaved grids use the common spacing of the left wall's 17 segments. -/
namespace HadwigerNelson.Certificate.Hole

abbrev step : ℤ := 540000000
abbrev cutoff : ℤ := 17*step

def width (z : ℤ) : ℤ :=
  let y := z.natAbs
  if y ≥ PartialWave.y0Int then 0 else
    let i := y/step.toNat
    let left := (PartialWave.leftKnots[i]?.getD (0,0)).2
    let right := (PartialWave.leftKnots[i+1]?.getD (0,0)).2
    Arithmetic.interpDown (i*step) left ((i+1)*step) right y

def height (dx dy z : ℤ) : ℤ :=
  let a := width z
  let b := width (z-dy)
  min (2*a) (min (2*b) (a+b-dx))

def segment (u v width : ℤ) : ℤ :=
  if 0 ≤ u then
    if 0 ≤ v then width*(u+v) else width*u^2/(u-v)
  else if 0 ≤ v then width*v^2/(v-u) else 0

def gridTick (dy : ℤ) (i : ℕ) : ℤ :=
  let base := ((i/2:ℕ):ℤ)*step-cutoff
  max (dy-cutoff) (min cutoff (base + if i%2=0 then 0 else dy%step))

def slab (dx dy : ℤ) (i : ℕ) : ℤ :=
  let a := gridTick dy i
  let b := gridTick dy (i+1)
  segment (height dx dy a) (height dx dy b) (b-a)

def ticks (dx dy : ℤ) : ℤ :=
  if 2*cutoff ≤ dy then 0 else (Array.ofFn (fun i : Fin 68 => slab dx dy i.val)).sum

def overlap (x y : ℚ) : ℚ :=
  let S := (PartialWave.scale:ℚ)
  (ticks (x*S).ceil (y*S).ceil : ℚ)/(2*S*PartialWave.xInt)

end HadwigerNelson.Certificate.Hole
