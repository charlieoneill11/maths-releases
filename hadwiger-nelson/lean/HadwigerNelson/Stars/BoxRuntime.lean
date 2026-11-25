import HadwigerNelson.Angular.Runtime

/-! The complete-wave star rectangles, dyadic angular traversal and colour
classifier. Source and destination rectangle coordinates use units of 10⁻¹². -/

namespace HadwigerNelson.Stars
open Arithmetic
open Angular (Box)
open CompleteWave (height scale profile step xInt)

namespace BoxCheck

inductive Status where
  | outside | uncertain | inside
  deriving Repr, DecidableEq, Inhabited, Ord

/-- Interval enclosure for the interpolated right wall of the positive tile. -/
def wall (y : Int) : Int × Int :=
  let k := (y / step).toNat
  let a : Int := profile[k]?.getD 0
  let t := y % step
  if t = 0 then (a,a) else
    let b : Int := profile[k+1]?.getD 0
    let n := (b-a)*t
    (a+n/step, a+ceilDiv n step)

def peak : Int := (profile[1024]?.getD 0 : Nat)

/-- Check the intersection with an individual column and vertical strip.
The test concerns the open box, so equality at an excluded seam is harmless. -/
def strip (lo hi low high : Int) (j : Int) : Status :=
  let h : Int := height
  let a := min h (max 0 (low-j*h))
  let b := min h (max 0 (high-j*h))
  if b ≤ a then .outside else
    let l := wall a
    let r := wall b
    if j*h ≤ low && high ≤ (j+1)*h && 0 ≤ lo && hi ≤ min l.1 r.1 then .inside else
      let top := if a ≤ h/2 && h/2 ≤ b then peak else max l.2 r.2
      if lo < top then .uncertain else .outside

def merge : Status → Status → Status
  | .inside, _ | _, .inside => .inside
  | .uncertain, _ | _, .uncertain => .uncertain
  | _, _ => .outside

def scanRows (f : Nat → Status) : Nat → Status
  | 0 => .outside
  | n+1 => merge (scanRows f n) (f n)

def code (colour : Nat) (j : Int) : Nat :=
  (if colour ≤ 3 then 1 else 4) + (-j % 3).toNat

def checkRows (lo hi low high : Int) (colour : Nat) : Status :=
  let h : Int := height
  let first := low/h
  scanRows (fun offset =>
    let j := first+(offset : Int)
    if code colour j == colour then strip lo hi low high j else .outside)
    (high/h-first+1).toNat

/-- Release labels 1–3 are on the positive side of a column centre, 4–6
are on its reflected side. -/
def column (box : Box) (colour : Nat) (m : Int) : Status :=
  let h : Int := height
  let u : Int := 2*xInt
  let (lo,hi) := if colour ≤ 3 then (box.xlo-m*u, box.xhi-m*u)
                                else (m*u-box.xhi, m*u-box.xlo)
  if hi ≤ 0 || peak ≤ lo then .outside else
    checkRows lo hi (box.ylo-3*m*h/2) (box.yhi-3*m*h/2) colour

def classify (box : Box) (colour : Nat) : Status :=
  merge (merge (merge (column box colour (-2)) (column box colour (-1)))
    (column box colour 0)) (merge (column box colour 1) (column box colour 2))

/-- A signed quarter-turn of the closed rational direction enclosure. -/
def quadrant (q : Nat) (b : Box) : Box :=
  match q % 4 with
  | 0 => b
  | 1 => ⟨-b.yhi, -b.ylo, b.xlo, b.xhi⟩
  | 2 => ⟨-b.xhi, -b.xlo, -b.yhi, -b.ylo⟩
  | _ => ⟨b.ylo, b.yhi, -b.xhi, -b.xlo⟩

def destination (source offset : Box) : Box :=
  ⟨source.xlo+offset.xlo, source.xhi+offset.xhi,
   source.ylo+offset.ylo, source.yhi+offset.yhi⟩

structure Span where
  quadrant : Nat
  start : Nat
  stop : Nat
  coeff : Int
  radius : Int
  deriving Inhabited, Repr

def appendSpan (out : Array Span) (s : Span) : Array Span :=
  match out.back? with
  | none => #[s]
  | some last =>
    if last.quadrant == s.quadrant && last.stop == s.start &&
       last.coeff == s.coeff && last.radius == s.radius then
      out.pop.push {last with stop := s.stop}
    else out.push s

/-- The midpoint and radius of the possible native-minus-alternate
indicator, both multiplied by two. -/
def signedStep (native alt : Status) : Int × Int :=
  if native == .inside then (2,0)
  else if alt == .inside then (-2,0)
  else
    let n := if native == .outside then 0 else 1
    let a := if alt == .outside then 0 else 1
    (n-a,n+a)

def resolution : Nat := 2^17

def traverse (source : Box) (other q : Nat) : Nat → Nat → Array Span → Array Span
  | 0, a, acc =>
    let b := destination source (quadrant q (Angular.halfAngleBox resolution a (a+1)))
    let (c,r) := signedStep (classify b 1) (classify b other)
    appendSpan acc ⟨q,a,a+1,c,r⟩
  | depth+1, a, acc =>
    let stop := a+2^(depth+1)
    let b := destination source (quadrant q (Angular.halfAngleBox resolution a stop))
    let (c,r) := signedStep (classify b 1) (classify b other)
    if r == 0 then appendSpan acc ⟨q,a,stop,c,r⟩
    else traverse source other q depth (a+2^depth) (traverse source other q depth a acc)

def runs (source : Box) (other : Nat) : Array Span :=
  let first := traverse source other 0 17 0 #[]
  let second := traverse source other 1 17 0 first
  let third := traverse source other 2 17 0 second
  traverse source other 3 17 0 third

structure Source where
  xlo : Int
  xhi : Int
  ylo : Int
  yhi : Int
  other : Nat
  deriving Inhabited, Repr

def Source.box (s : Source) : Box :=
  ⟨s.xlo*10^6,s.xhi*10^6,s.ylo*10^6,s.yhi*10^6⟩

def Source.area (s : Source) : Int := (s.xhi-s.xlo)*(s.yhi-s.ylo)
def Source.separate (s : Source) : Bool := s.xlo ≥ 600 || s.ylo ≥ 1050

/-- The 14,464 harmonic boxes in millionths, indexed in the release order. -/
def source (i : Nat) : Source := Id.run do
  let bands : Array (Int × Int) := #[(0,5),(5,15),(15,35),(35,65)]
  let (a,b) := bands[i%4]?.getD (0,0)
  if i < 1200 then
    let y : Int := (i/4)*20
    return ⟨a,b,y,y+20,4⟩
  if i < 4464 then
    let t := (i-1200)/4
    let x : Int := if t < 296 then 80+t*20 else 866000+(t-296)*20
    return ⟨x,x+20,a,b,2⟩
  let y : Int := ((i-4464)/4)*100
  let r := (wall (y*10^6)).1/10^6
  let narrow : Array (Int × Int) := #[(0,10),(10,30),(30,60),(60,95)]
  let (a,b) := narrow[i%4]?.getD (0,0)
  return ⟨r-b,r-a,y,y+100,6⟩

/-- The 252 native-only boxes in the saturation rectangle. -/
def saturated (i : Nat) : Source :=
  let x : Int := (i%12)*50
  let y : Int := (i/12)*50
  ⟨x,x+50,y,y+50,4⟩

end BoxCheck
end HadwigerNelson.Stars
