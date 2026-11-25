/-! Fixed-width search for an independent plane with a prescribed number of set bits. -/

namespace SevenCycleRuntime.PlaneSearch

@[inline] def cell (i : Nat) : UInt64 := (1 : UInt64) <<< i.toUInt64

/-- Enumerate choices below bit i. A full set is passed to the continuation. -/
def all (blocked : Vector UInt64 49) (visit : UInt64 → Bool)
    (i need : Nat) (available chosen : UInt64) : Bool :=
  if need == 0 then visit chosen
  else if need > i || available == 0 then true
  else match i with
  | 0 => true
  | j+1 =>
    let b := cell j
    if (available &&& b) == 0 then all blocked visit j need available chosen
    else
      let rest := available ^^^ b
      all blocked visit j (need-1) (rest &&& ~~~blocked[j]!) (chosen ||| b) &&
        all blocked visit j need rest chosen

end SevenCycleRuntime.PlaneSearch
