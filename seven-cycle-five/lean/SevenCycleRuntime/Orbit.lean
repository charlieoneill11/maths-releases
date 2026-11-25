import Init

/-! Native cube transformations over the seven-by-seven-by-seven torus.
A signed permutation is supplied as a complete inverse address table.
The mathematical interpretation and coverage proofs are in
`SevenCycle.Bitsets.Orbit`. -/

namespace SevenCycleRuntime.Orbit

abbrev Cube := Vector UInt64 7
abbrev AddressMap := Vector (Fin 343) 343

@[inline] def read (c : Cube) (j : Fin 343) : Bool :=
  (c.get ⟨j.val/49, by omega⟩).toNat.testBit (j.val % 49)

def lowBits (f : Nat → Bool) : Nat → UInt64
  | 0 => 0
  | n+1 => lowBits f n ||| (if f n then UInt64.ofNat (2^n) else 0)

def orient (c : Cube) (m : AddressMap) : Cube :=
  Vector.ofFn fun h => lowBits (fun j => read c (m.get (Fin.ofNat 343 (49*h.val+j)))) 49

@[inline] def step (column : Bool) (p : UInt64) : UInt64 :=
  if column then
    ((p <<< 1) &&& (0x1fbf7efdfbf7e : UInt64)) ||| ((p >>> 6) &&& (0x40810204081 : UInt64))
  else
    ((p <<< 7) &&& (0x1ffffffffff80 : UInt64)) ||| ((p >>> 42) &&& (0x7f : UInt64))

def move (column : Bool) (p : UInt64) : Nat → UInt64
  | 0 => p
  | n+1 => step column (move column p n)

def lateral (c : Cube) (column : Bool) (v : Fin 7) : Cube :=
  c.map fun p => move column p v.val

def rotateHeight (c : Cube) (v : Fin 7) : Cube :=
  Vector.ofFn fun h : Fin 7 => c.get (Fin.ofNat 7 (h.val + 7 - v.val))

def translations (c : Cube) : Array Cube :=
  (Array.finRange 7).flatMap fun y =>
    let cy := lateral c false y
    (Array.finRange 7).flatMap fun z =>
      let cyz := lateral cy true z
      (Array.finRange 7).map fun x => rotateHeight cyz x

def images (maps : Array AddressMap) (c : Cube) : Array Cube :=
  maps.flatMap fun m => translations (orient c m)

end SevenCycleRuntime.Orbit
