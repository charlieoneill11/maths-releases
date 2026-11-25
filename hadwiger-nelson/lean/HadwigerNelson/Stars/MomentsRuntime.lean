import HadwigerNelson.Stars.BoxRuntime
import HadwigerNelson.Arithmetic.GaussianInt
import Batteries.Data.Nat.Basic

/-! Outward integer enclosures for the complete wave's mean and first 56
Fourier magnitudes on each source rectangle. -/

namespace HadwigerNelson.Stars.BoxCheck
open Arithmetic

def phaseScale : Int := 2^80
def quant : Int := 10^10
def thresholdScale : Int := 10^5
def harmonics : Nat := 56

def piLow : Int := 314159265358979323846
def piDen : Int := 10^20

/-- Lower bound, in units of 1/quant, for dividing m/phaseScale by kπ. -/
def normalise (m : Int) (k : Int) : Int :=
  m*quant*piDen / (k*phaseScale*(if m < 0 then piLow else piLow+1))

structure Arc where
  low : Int
  high : Int
  deriving Repr, Inhabited

/-- From angle i/N to (i+1)/N in the tangent-half-angle parameter. -/
def arcStep (i : Nat) : Arc :=
  let n : Int := resolution
  let j : Int := i
  let den := n*n+j*(j+1)
  ⟨2*phaseScale*n*(3*den*den-n*n) / (3*den*den*den), ceilDiv (2*phaseScale*n) den⟩

/-- The accumulator stores the current outward sums and the inclusive prefix table. -/
def arcPrefix (n : Nat) : Arc × Array Arc :=
  n.fold (fun i _ (state : Arc × Array Arc) =>
    let delta := arcStep i
    let arc : Arc := ⟨state.1.low+delta.low,state.1.high+delta.high⟩
    (arc,state.2.push arc)) (⟨0,0⟩,#[⟨0,0⟩])

def arcTable : Array Arc := (arcPrefix resolution).2

def spanArc (table : Array Arc) (s : Span) : Arc :=
  let a := table[s.start]?.getD default
  let b := table[s.stop]?.getD default
  ⟨b.low-a.low,b.high-a.high⟩

structure Triple where
  x : Int
  y : Int
  den : Int
  deriving Inhabited, Repr

def phaseTriple (q i : Nat) : Triple :=
  let n : Int := resolution
  let j : Int := i
  let d := n*n+j*j
  let a := n*n-j*j
  let b := 2*n*j
  match q%4 with
  | 0 => ⟨a,b,d⟩ | 1 => ⟨-b,a,d⟩ | 2 => ⟨-a,-b,d⟩ | _ => ⟨b,-a,d⟩

/-- The exact unit ray has both components within one scale tick of base. -/
def phaseBase (q i : Nat) : GaussianInt :=
  let t := phaseTriple q i
  GaussianInt.ofRay phaseScale t.x t.y t.den

structure Row where
  area : Int
  mean : Int
  magnitude : Array Int
  separate : Bool
  deriving Repr, Inhabited

/-- The per-span tables are shared by all harmonics of one source. -/
structure SpanMoments where
  source : Span
  mean : Int
  error : Int
  mass : Int
  start : Array GaussianInt
  stop : Array GaussianInt
  deriving Inhabited

def prepareSpan (table : Array Arc) (p : Span) : SpanMoments :=
  let arc := spanArc table p
  let c := p.coeff-p.radius
  let phases (i : Nat) := if p.coeff == 0 then #[] else
    GaussianInt.powerTable phaseScale (phaseBase p.quadrant i) harmonics
  ⟨p,c*(if c < 0 then arc.high else arc.low),p.radius*arc.high,p.coeff.natAbs,
   phases p.start,phases p.stop⟩

def SpanMoments.term (m : SpanMoments) (k : Nat) : GaussianInt :=
  let u := m.start[k]?.getD default
  let v := m.stop[k]?.getD default
  ⟨m.source.coeff*(u.re-v.re),m.source.coeff*(u.im-v.im)⟩

def spanSum (terms : Array SpanMoments) (f : SpanMoments → Int) : Int :=
  terms.foldl (fun a s => a+f s) 0

/-- Apply the allowances for both the signed angular radius and the
fixed-point error (at most 6k ticks at each endpoint of a k-th moment). -/
def momentsFrom (table : Array Arc) (spans : Array Span) (s : Source) : Row :=
  let terms := spans.map (prepareSpan table)
  let mean := spanSum terms SpanMoments.mean
  let err := spanSum terms SpanMoments.error
  let mass := spanSum terms SpanMoments.mass
  let mag := Array.ofFn fun (k : Fin harmonics) =>
    let x := spanSum terms (fun m => (m.term k.val).re)
    let y := spanSum terms (fun m => (m.term k.val).im)
    let root : Int := ((x*x+y*y).toNat.sqrt : Nat)
    max 0 (normalise (root/(k.val+1 : Nat)-12*mass-err) 4)
  ⟨s.area,normalise mean 4,mag,s.separate⟩

def moments (table : Array Arc) (s : Source) : Row :=
  momentsFrom table (runs s.box s.other) s

def nativeTicks (table : Array Arc) (spans : Array Span) : Int :=
  spans.foldl (fun n p => n+(if p.coeff == 2 && p.radius == 0 then (spanArc table p).low else 0)) 0

def nativeFraction (table : Array Arc) (s : Source) : Int :=
  normalise (nativeTicks table (runs s.box s.other)) 2

end HadwigerNelson.Stars.BoxCheck
