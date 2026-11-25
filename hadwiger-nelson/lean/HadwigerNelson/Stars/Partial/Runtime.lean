import HadwigerNelson.Data.PartialWave
import HadwigerNelson.Stars.MomentsRuntime

/-! Integer classification of the partial wave and the four source families of §3.4.
Both boundaries are rounded outwards. The native-only sources have alternate code zero. -/

namespace HadwigerNelson.Stars.PartialCheck
open Arithmetic BoxCheck
open Angular (Box)
open PartialWave (xInt)

/-- Both walls have a reflected height profile on the second half-strip. -/
def reflectedHeight (y : Int) : Int := min y (500000000000-y)

def wallPair (atKnot : Nat → Nat × Nat) (step y : Int) : Int × Int :=
  let i := (y/step).toNat
  let w : Int := (atKnot i).2
  let t := y%step
  if t == 0 then (w,w) else
    let next : Int := (atKnot (i+1)).2
    (w+(next-w)*t/step,w+ceilDiv ((next-w)*t) step)

def left (y : Int) : Int × Int :=
  let v := reflectedHeight y
  if 9180000000 ≤ v then (0,0) else wallPair PartialWave.leftKnot 540000000 v

def right (y : Int) : Int × Int :=
  wallPair PartialWave.rightKnot 976562500 (reflectedHeight y)

def peak : Int := (PartialWave.rightKnot 256).2

def strip (lo hi low high j : Int) : Status :=
  let h : Int := 500000000000
  let a := max 0 (low-j*h)
  let b := min h (high-j*h)
  if b < a then .outside else
    let l := left a
    let l' := left b
    let r := right a
    let r' := right b
    let mid := a ≤ h/2 && h/2 ≤ b
    let lower := if mid then 0 else min l.1 l'.1
    let upper := if mid then peak else max r.2 r'.2
    if max l.2 l'.2 < lo && hi < min r.1 r'.1 && j*h < low && high < (j+1)*h then
      .inside
    else if lower ≤ hi && lo ≤ upper then .uncertain else .outside

def column (box : Box) (colour : Nat) (m : Int) : Status :=
  let h : Int := 500000000000
  let u : Int := 2*xInt
  let (lo,hi) := if colour ≤ 3 then (box.xlo-m*u, box.xhi-m*u)
                                else (m*u-box.xhi, m*u-box.xlo)
  if hi < 0 || 1000000000000 < lo then .outside else
    let low := box.ylo-750000000000*m
    let high := box.yhi-750000000000*m
    let first := low/h
    scanRows (fun i =>
      let j := first+(i : Int)
      if code colour j == colour then strip lo hi low high j else .outside)
      (high/h-first+1).toNat

def classify (box : Box) (colour : Nat) : Status :=
  merge (merge (column box colour (-1)) (column box colour 0)) (column box colour 1)

/-- A lower step is exact for a constant span. At the finest subdivision,
it retains the least signed value compatible with the two statuses. -/
def lowerStep (native other : Status) : Int × Bool :=
  if native == .inside then (1,true)
  else if other == .inside then (-1,true)
  else if native == .outside && other == .outside then (0,true)
  else (if other == .outside then 0 else -1,false)

def node (src : Box) (other q a b : Nat) : Int × Bool :=
  let dest := destination src (quadrant q (Angular.halfAngleBox resolution a b))
  lowerStep (classify dest 1) (if other == 0 then .outside else classify dest other)

def visit (src : Box) (other q : Nat) : Nat → Nat → Array Span → Array Span
  | 0, a, acc =>
    let c := (node src other q a (a+1)).1
    if c == 0 then acc else appendSpan acc ⟨q,a,a+1,c,0⟩
  | depth+1, a, acc =>
    let b := a+2^(depth+1)
    let (c,fixed) := node src other q a b
    if fixed then
      if c == 0 then acc else appendSpan acc ⟨q,a,b,c,0⟩
    else visit src other q depth (a+2^depth) (visit src other q depth a acc)

def runs (src : Box) (other : Nat) : Array Span :=
  let q0 := visit src other 0 17 0 #[]
  let q1 := visit src other 1 17 0 q0
  let q2 := visit src other 2 17 0 q1
  visit src other 3 17 0 q2

/-- The 132,621 harmonic and 4,122 native-only rectangles in millionths. -/
def source (i : Nat) : Source := Id.run do
  let small : Array (Int × Int) := #[(1,4),(4,10),(10,20),(20,40),(40,70)]
  if i < 124995 then
    let y : Int := 1+(i/5)*10
    let x := (right (y*10^6)).1/10^6
    let (a,b) := small[i%5]?.getD (0,0)
    return ⟨x-b,x-a,y,y+10,6⟩
  if i < 128531 then
    let t := i-124995
    let y : Int := 9170+(t/8)*20
    let x := (left (y*10^6)).1/10^6+1
    let bands : Array (Int × Int) := #[(0,2),(2,5),(5,12),(12,25),(25,45),(45,80),(80,135),(135,200)]
    let (a,b) := bands[t%8]?.getD (0,0)
    return ⟨x+a,x+b,y,y+20,4⟩
  if i < 132621 then
    let t := i-128531
    let r := t/5
    let x : Int := if r < 268 then 4300+r*25 else 861000+(r-268)*25
    let bands : Array (Int × Int) := #[(1,4),(4,10),(10,20),(20,40),(40,75)]
    let (a,b) := bands[t%5]?.getD (0,0)
    return ⟨x,x+25,a,b,2⟩
  let t := i-132621
  let y : Int := 5+(t/9)*20
  let x := (left (y*10^6)).1/10^6+1
  let bands : Array (Int × Int) := #[(0,5),(5,15),(15,30),(30,55),(55,90),(90,150),(150,240),(240,360),(360,540)]
  let (a,b) := bands[t%9]?.getD (0,0)
  return ⟨x+a,x+b,y,y+20,0⟩

end HadwigerNelson.Stars.PartialCheck
