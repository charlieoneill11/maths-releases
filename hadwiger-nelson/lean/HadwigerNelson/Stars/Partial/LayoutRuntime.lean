import HadwigerNelson.Stars.Partial.Runtime

/-! Linear-size checks of the four rectangle families of §3.4. Sources are
indexed in the order of the release. A row runs horizontally on the two
walls and vertically on the bottom edge. Coordinates are in millionths. -/

namespace HadwigerNelson.Stars.PartialCheck.Layout
open BoxCheck (Source)

inductive Family where
  | right | left | bottom | native
  deriving DecidableEq, Inhabited

def family (i : Nat) : Family :=
  if i < 124995 then .right else if i < 128531 then .left
  else if i < 132621 then .bottom else .native

def base : Family → Nat
  | .right => 0 | .left => 124995 | .bottom => 128531 | .native => 132621

def lanes : Family → Nat
  | .right => 5 | .left => 8 | .bottom => 5 | .native => 9

def alternate : Family → Nat
  | .right => 6 | .left => 4 | .bottom => 2 | .native => 0

/-- Three vertical strips separate the right, bottom and left sources. The
two families in the left strip are separated horizontally at height 9170. -/
def region : Family → Source
  | .right => ⟨874750,1000000,0,250000,0⟩
  | .left => ⟨0,4300,9170,250000,0⟩
  | .bottom => ⟨4300,874750,0,250000,0⟩
  | .native => ⟨0,4300,0,9170,0⟩

def rowStart : Family → Nat → Int
  | .right,k => 1+10*(k : Int)
  | .left,k => 9170+20*(k : Int)
  | .bottom,k => 4300+25*(k : Int)+(if k<268 then 0 else 850000)
  | .native,k => 5+20*(k : Int)

def rowWidth : Family → Int
  | .right => 10 | .left => 20 | .bottom => 25 | .native => 20

def axisLo (f : Family) (s : Source) := if f = .bottom then s.xlo else s.ylo
def axisHi (f : Family) (s : Source) := if f = .bottom then s.xhi else s.yhi

def separate (s t : Source) : Bool :=
  s.xhi ≤ t.xlo || t.xhi ≤ s.xlo || s.yhi ≤ t.ylo || t.yhi ≤ s.ylo

def entry (i : Nat) : Bool :=
  let f := family i
  let s := source i
  let t := i-base f
  let n := lanes f
  let first := t/n*n + base f
  let lo := rowStart f (t/n)
  let zone := region f
  (s.xlo < s.xhi && s.ylo < s.yhi) &&
    (zone.xlo ≤ s.xlo && s.xhi ≤ zone.xhi && zone.ylo ≤ s.ylo && s.yhi ≤ zone.yhi) &&
    (lo ≤ axisLo f s && axisHi f s ≤ lo+rowWidth f) &&
    (s.other == alternate f && classify s.box 1 == .inside) &&
    (Array.range n).all (fun k => k == t%n || separate s (source (first+k)))

def check : Bool := (Array.range 136743).all entry

end HadwigerNelson.Stars.PartialCheck.Layout
