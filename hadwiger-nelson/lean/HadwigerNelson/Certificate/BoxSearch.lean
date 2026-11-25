import HadwigerNelson.Certificate.Objective

namespace HadwigerNelson.Certificate.ParameterBoxes

structure Range where
  lo : Nat
  hi : Nat
  deriving Repr

structure Box where
  m : Range
  s : Range
  j : Range
  deriving Repr

def Range.interval (r : Range) : Interval := ⟨r.lo,r.hi⟩

def Box.clip (b : Box) : Box :=
  {b with s.hi := min b.s.hi (10689-b.j.lo), j.hi := min b.j.hi (10689-b.s.lo)}

def Box.omitted (b : Box) : Interval :=
  ⟨(b.s.lo+b.j.lo:Nat),(min 10689 (b.s.hi+b.j.hi):Nat)⟩

def Box.upper (b : Box) : ℚ :=
  let m := b.m.interval
  let s := b.s.interval
  let j := b.j.interval
  let v := variance m
  let upper := (firstTerms m s j v).hi
  if upper < 1 then upper else
    let bgt := budgets m s j b.omitted v
    upper - max (credit bgt (230/10^10) (79/10^10) (980/10^10)).lo
      (credit bgt (259/10^10) (93/10^10) (1100/10^10)).lo

def Range.cut (r : Range) : Range × Range :=
  let mid := (r.lo+r.hi)/2
  (⟨r.lo,mid⟩,⟨mid+1,r.hi⟩)

def Box.split (b : Box) : Box × Box :=
  let wm := b.m.hi-b.m.lo
  let ws := 12*(b.s.hi-b.s.lo)
  let wj := 12*(b.j.hi-b.j.lo)
  if ws ≤ wm && wj ≤ wm then
    ({b with m:=b.m.cut.1},{b with m:=b.m.cut.2})
  else if wj ≤ ws then
    ({b with s:=b.s.cut.1},{b with s:=b.s.cut.2})
  else
    ({b with j:=b.j.cut.1},{b with j:=b.j.cut.2})

def checkBox : Nat → Box → Bool
  | 0, _ => false
  | n+1, b =>
    if 10689 < b.s.lo+b.j.lo then true else
      let b := b.clip
      if b.upper < 1 then true else
        let (l,r) := b.split
        checkBox n l && checkBox n r

def fullBox : Box := ⟨⟨0,403078⟩,⟨0,10689⟩,⟨0,10689⟩⟩

end HadwigerNelson.Certificate.ParameterBoxes
