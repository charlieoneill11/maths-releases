import SevenCycleRuntime.Middle

/-! # Counts of known words on a transverse slice of a three-level slab -/

namespace SevenCycle.Adjacent.BandCounts

abbrev Cube := Vector UInt64 7

@[inline] def sliceMask (a : Fin 3) (c : Fin 7) : Cube :=
  match a.val with
  | 0 => Vector.ofFn fun x => if x = c then 0x1ffffffffffff else 0
  | 1 => Vector.replicate 7 ((127 : UInt64) <<< (7*c.val).toUInt64)
  | _ => Vector.replicate 7 ((0x40810204081 : UInt64) <<< c.val.toUInt64)

@[inline] def sliceCount (s : Cube) (a : Fin 3) (c : Fin 7) : Nat :=
  Middle.count (Vector.zipWith (· &&& ·) s (sliceMask a c))

/-- Count either anchor band on the transverse slice and subtract the middle,
which is present in both bands. -/
@[inline] def known (s t u : Cube) (a : Fin 3) (c : Fin 7) : Nat :=
  sliceCount s a c + sliceCount t a c - sliceCount u a c

end SevenCycle.Adjacent.BandCounts
