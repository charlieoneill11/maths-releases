import HadwigerNelson.Stars.Partial.Runtime

/-! Partial-wave angular coefficients on a grid of denominator 10¹².
The cache stores endpoint powers shared between different source rectangles. -/

namespace HadwigerNelson.Stars.PartialCheck
open Arithmetic BoxCheck

def frequencyCount : Nat := 309
def scale : Int := 10^12

def arcStep (i : Nat) : Arc :=
  let n : Int := resolution
  let j : Int := i
  let den := n*n+j*(j+1)
  ⟨(2*scale*n)/den-1,ceilDiv (2*scale*n) den⟩

def arcPrefix (n : Nat) : Arc × Array Arc :=
  n.fold (fun i _ (state : Arc × Array Arc) =>
    let delta := arcStep i
    let next : Arc := ⟨state.1.low+delta.low,state.1.high+delta.high⟩
    (next,state.2.push next)) (⟨0,0⟩,#[⟨0,0⟩])

def arcTable : Array Arc := (arcPrefix resolution).2

def normalized (v : Int) : Int :=
  v*quant*10000000 / (2*scale*(if v < 0 then 31415926 else 31415927))

def powerEntry (q i : Nat) : Array GaussianInt :=
  let t := phaseTriple q i
  GaussianInt.powerTable scale (GaussianInt.ofRay scale t.x t.y t.den) frequencyCount

abbrev Cache := Std.HashMap (Nat × Nat) (Array GaussianInt)

def loadPowers (cache : Cache) (q i : Nat) : Cache × Array GaussianInt :=
  match cache[(q,i)]? with
  | some powers => (cache,powers)
  | none =>
    let powers := powerEntry q i
    (cache.insert (q,i) powers,powers)

structure PairMoments where
  sign : Int
  start : Array GaussianInt
  stop : Array GaussianInt

def prepare (need : Bool) (spans : Array Span) (cache : Cache) : Cache × Array PairMoments :=
  if need then
    spans.foldl (fun (cache,acc) p =>
      let (cache,a) := loadPowers cache p.quadrant p.start
      let (cache,b) := loadPowers cache p.quadrant p.stop
      (cache,acc.push ⟨p.coeff,a,b⟩)) (cache,#[])
  else (cache,#[])

def meanTicks (table : Array Arc) (spans : Array Span) : Int :=
  spans.foldl (fun a p =>
    let len := spanArc table p
    a+p.coeff*(if p.coeff<0 then len.high else len.low)) 0

def PairMoments.term (t : PairMoments) (k : Nat) : GaussianInt :=
  let a := t.start[k]?.getD default
  let b := t.stop[k]?.getD default
  ⟨t.sign*(a.re-b.re),t.sign*(a.im-b.im)⟩

def sumTerms (terms : Array PairMoments) (k : Nat) : GaussianInt :=
  terms.foldl (fun p t =>
    let v := t.term k
    ⟨p.re+v.re,p.im+v.im⟩) ⟨0,0⟩

def magnitude (terms : Array PairMoments) (k : Nat) : Int :=
  let z := sumTerms terms k
  let r : Int := ((z.re*z.re+z.im*z.im).toNat.sqrt : Nat)
  normalized (max 0 (r/(k+1 : Nat)-12*terms.size))

structure Row where
  area : Int
  mean : Int
  spectrum : Array Int
  deriving Repr, Inhabited

def row (arcs : Array Arc) (s : Source) (cache : Cache) : Cache × Row :=
  let spans := runs s.box s.other
  let (cache,terms) := prepare (s.other != 0) spans cache
  let mag := if s.other == 0 then #[] else
    Array.ofFn fun k : Fin frequencyCount => magnitude terms k
  (cache,⟨s.area,normalized (meanTicks arcs spans),mag⟩)

end HadwigerNelson.Stars.PartialCheck
