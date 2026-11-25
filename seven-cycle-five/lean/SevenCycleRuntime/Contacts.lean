import SevenCycleRuntime.TypeThree

namespace SevenCycle.Adjacent.Contacts

abbrev Cube := Vector UInt64 7
abbrev Key := UInt64 × UInt64
abbrev Index := Std.HashMap Key (Array UInt64)
abbrev Height := Fin 7

@[inline] def key (w : Cube) : Key := (TypeThree.cutX w 0, TypeThree.cutX w 1)

@[inline] def middle (w : Cube) : UInt64 := w.get 1 &&& 0x1ffffffffffff

def insert (m : Index) (w : Cube) : Index :=
  m.alter (key w) fun v =>
    let xs := v.getD #[]
    some (if xs.contains (middle w) then xs else xs.push (middle w))

/-- Enumerate orbit images once per class. Deduplication keeps a single copy of
each possible middle plane of an ordered pair of adjacent crossing cuts. -/
def index (orbits : Cube → Array Cube) (rows : Array Cube) : Index :=
  rows.foldl (init := {}) fun m r => (orbits r).foldl insert m

@[inline] def anchorKey (s t : Cube) (k : Fin 3) (j : Height) : Key :=
  (TypeThree.fastCut s k j, TypeThree.fastCut t k j)

/-- Store the later start as center. The earlier start is center minus gap. -/
def centers (idx : Index) (s t : Cube) (k : Fin 3) (gap : Height) : Array Height :=
  let starts := Vector.ofFn (n := 7) fun j => idx.contains (anchorKey s t k j)
  (Array.finRange 7).filter fun c => starts.get c && starts.get (c-gap)

def checkContacts (idx : Index) (s t : Cube) (gaps : Vector Height 3)
    (next : Height → Height → Height → Bool) : Bool :=
  let xs := centers idx s t 0 (gaps.get 0)
  xs.isEmpty ||
    let ys := centers idx s t 1 (gaps.get 1)
    ys.isEmpty ||
      let zs := centers idx s t 2 (gaps.get 2)
      xs.all fun x => ys.all fun y => zs.all (next x y)

end SevenCycle.Adjacent.Contacts
