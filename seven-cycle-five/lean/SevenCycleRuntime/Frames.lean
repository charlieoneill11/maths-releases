import SevenCycleRuntime.SlabJoin

namespace SevenCycle.Adjacent.SlabJoin

/-- Output-coordinate to source-coordinate convention. -/
abbrev AxisOrder := Vector (Fin 4) 4

def orders : Array AxisOrder := #[
  #v[0,1,2,3],
  #v[0,1,3,2],
  #v[0,2,1,3],
  #v[0,2,3,1],
  #v[0,3,1,2],
  #v[0,3,2,1],
  #v[1,0,2,3],
  #v[1,0,3,2],
  #v[1,2,0,3],
  #v[1,2,3,0],
  #v[1,3,0,2],
  #v[1,3,2,0],
  #v[2,0,1,3],
  #v[2,0,3,1],
  #v[2,1,0,3],
  #v[2,1,3,0],
  #v[2,3,0,1],
  #v[2,3,1,0],
  #v[3,0,1,2],
  #v[3,0,2,1],
  #v[3,1,0,2],
  #v[3,1,2,0],
  #v[3,2,0,1],
  #v[3,2,1,0]
]

def identityOrder : AxisOrder := #v[0,1,2,3]

@[inline] def transformedSite (p : AxisOrder) (signs j : Nat) : Nat :=
  let v := fun k : Fin 4 =>
    let n := coords j p[k]
    if signs.testBit k.val then (7-n)%7 else n
  343 * v 0 + 49 * v 1 + 7 * v 2 + v 3

def readSlab (row : String) : Array Nat :=
  let b := row.toUTF8
  let digit := fun (byte : UInt8) =>
    let t := byte.toNat
    if t ≤ 90 && 65 ≤ t then t-65
    else if 97 ≤ t && t ≤ 122 then t-97+26
    else if 48 ≤ t && t ≤ 57 then t-48+52
    else if t == 45 then 62 else 63
  (Array.range (b.size / 2)).map fun k => 64 * digit b[2*k]! + digit b[2*k+1]!

def oneBitMap (p : AxisOrder) (signs : Nat) : Array Nat :=
  (Array.range 2401).map fun j => 1 <<< transformedSite p signs j

def movedMask (m : Array Nat) (sites : Array Nat) : Nat :=
  sites.foldl (init := 0) fun acc i => acc ||| (m[i]?.getD 0)

def rawRegion (k : Fin 4) : Nat := maskUpTo (fun j =>
  let n := coords j k
  n == 0 || n == 1 || n == 6) 2401

def regionMasks : Vector Nat 4 := Vector.ofFn rawRegion

def transforms (k : Fin 4) : Array (AxisOrder × Nat) :=
  if k = 0 then #[(identityOrder, 0)] else
    (orders.filter fun p => p[k] == 0).flatMap fun p => (Array.range 16).map fun s => (p,s)

/-- Nat hashing retains only its low machine word. Fold every occupied bit
into the bucket index; equality still compares the entire physical slab. -/
structure FrameMask where
  bits : Nat
deriving DecidableEq

instance : Hashable FrameMask where
  hash r := (r.bits % 18446744073709551557).toUInt64

def frameMasks (rows : Array (Array Nat)) (k : Fin 4) : Std.HashSet FrameMask :=
  (transforms k).foldl (init := {}) fun seen (p,s) =>
    let m := oneBitMap p s
    rows.foldl (init := seen) fun out sites => out.insert ⟨movedMask m sites⟩

def frameDomains (data : Array String) : Domains :=
  let rows := data.map readSlab
  Vector.ofFn fun k => ((frameMasks rows k).toArray.map fun r => cached regionMasks r.bits)

end SevenCycle.Adjacent.SlabJoin
