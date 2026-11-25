import HadwigerNelson.Certificate.Hole.Tables
import Mathlib.Data.Nat.Sqrt

/-! Exact rational quadratures for both profiles in Lemma 49. The small
quadrature uses directional rounding of the two hole walls. The medium
quadrature uses the two-grid integer overlap of Definition 18. -/

namespace HadwigerNelson.Centres.Quadrature
open Certificate.Hole (width overlap)

abbrev pic : ℚ := 10^12
abbrev piHi : ℚ := 355/113
abbrev unitCone : ℚ := 73/10000
abbrev deltaR : ℚ := 53/10000
abbrev delta : ℚ := 1837/250000

/-- An upper bound on the deficit in the distance between the centres.
The tests also verify its defining squared inequality at every chord. -/
def deficit (hi : ℚ) : ℚ :=
  2 - (((4-hi^2)*10^16).floor.toNat.sqrt : ℚ)/10^8

def rootGuard (hi : ℚ) : Bool :=
  0≤hi && hi≤2 && 0≤deficit hi && deficit hi≤2 && (2-deficit hi)^2 ≤ 4-hi^2

def widthLower (y : ℚ) : ℚ := (width (y*pic).ceil : ℚ)/pic

def widthUpper (y : ℚ) : ℚ :=
  let t := (y*pic).floor
  if t ≥ Certificate.Hole.cutoff then 0 else ((width t : ℚ) + 1)/pic

structure Small where
  lower : ℚ
  upper : ℚ
  angles : Nat
  heights : Nat
  target : ℚ

def small (k : Nat) : Small :=
  match k with
  | 0 => ⟨deltaR,2/100,32,48,79/10^10⟩
  | 1 => ⟨delta,2/100,32,48,230/10^10⟩
  | 2 => ⟨deltaR,6/1000,100,180,93/10^10⟩
  | 3 => ⟨6/1000,2/100,100,180,93/10^10⟩
  | 4 => ⟨delta,8/1000,100,180,259/10^10⟩
  | _ => ⟨8/1000,2/100,100,180,259/10^10⟩

def Small.dt (s : Small) : ℚ := min (365/100000) (s.lower/2)/s.angles
def Small.dy (s : Small) : ℚ := (9/1000)/s.heights
def smallWidth (s : Small) (j k : Nat) : ℚ :=
  let t := (j+1 : Nat)*s.dt
  let y := k*s.dy
  let a := deficit s.upper/2+t^2/2
  let b := a+unitCone^2/2
  max 0 (min (widthLower (y+s.dy+a)-t)
    (s.lower/2-widthUpper (max 0 (y-b))-b*t))

def smallTotal (s : Small) : ℚ :=
  let area := (Array.ofFn (fun j : Fin s.angles =>
    (Array.ofFn (fun k : Fin s.heights => smallWidth s j.val k.val)).sum)).sum
  8*s.dt*s.dy*area/(piHi*(PartialWave.xInt/pic))

def smallPass (s : Small) : Bool :=
  rootGuard s.upper && 0<s.angles && 0<s.heights && 0<s.lower && 0≤s.upper &&
    s.target ≤ smallTotal s

def breakpoint : Nat → ℚ
  | 0 => 2/100 | 1 => 4/100 | 2 => 8/100 | 3 => 12/100 | 4 => 16/100 | 5 => 18/100
  | k+6 => (190+(k:ℚ))/1000

def mAngles (fine : Bool) : Nat := if fine then 256 else 48
def mEnd (lo : ℚ) : ℚ := min (36/10000) (lo/2-unitCone)
def mTarget (fine : Bool) (lo : ℚ) : ℚ :=
  let intercept := if fine then 259/10^10 else 230/10^10
  let cost := if fine then 1100/10^10 else 980/10^10
  intercept-cost*(lo-delta)

def mediumTerm (fine : Bool) (i j : Nat) : ℚ :=
  let t := (j+1 : Nat)*(mEnd (breakpoint i)/mAngles fine)
  overlap (2*t) (deficit (breakpoint (i+1))+t^2)

def mediumTotal (fine : Bool) (i : Nat) : ℚ :=
  let dt := mEnd (breakpoint i)/mAngles fine
  2*dt/piHi*(Array.ofFn fun j : Fin (mAngles fine) => mediumTerm fine i j.val).sum

def mediumPass (fine : Bool) (i : Nat) : Bool :=
  rootGuard (breakpoint (i+1)) && 0<mEnd (breakpoint i) &&
    mTarget fine (breakpoint i) ≤ mediumTotal fine i

end HadwigerNelson.Centres.Quadrature
