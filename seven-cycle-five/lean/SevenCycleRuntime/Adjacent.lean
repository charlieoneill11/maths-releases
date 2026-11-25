import Init

namespace SevenCycleRuntime.Adjacent

def rowWeights : Vector Nat 128 :=
  Vector.ofFn fun i : Fin 128 => (BitVec.ofNat 7 i.val).cpopNatRec 7 0

@[inline] def rowIndex (p : UInt64) (offset : UInt64) : Fin 128 :=
  ⟨((p >>> offset) &&& 127).toNat, by
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)⟩

@[inline] def rowWeight (p : UInt64) (offset : UInt64) : Nat :=
  rowWeights.get (rowIndex p offset)

/-- Counts the seven rows; a zero plane needs no table accesses. -/
@[inline] def maskCard (p : UInt64) : Nat :=
  if p = 0 then 0 else
    rowWeight p 0 + rowWeight p 7 + rowWeight p 14 + rowWeight p 21 +
    rowWeight p 28 + rowWeight p 35 + rowWeight p 42

/-- Seven unboxed fields in the native representation, one per height. -/
structure SupportCube where
  h0 : UInt64
  h1 : UInt64
  h2 : UInt64
  h3 : UInt64
  h4 : UInt64
  h5 : UInt64
  h6 : UInt64
deriving Inhabited

@[inline] def overlap (s t : SupportCube) : Nat :=
  maskCard (s.h0 &&& t.h0) + maskCard (s.h1 &&& t.h1) + maskCard (s.h2 &&& t.h2) +
  maskCard (s.h3 &&& t.h3) + maskCard (s.h4 &&& t.h4) + maskCard (s.h5 &&& t.h5) +
  maskCard (s.h6 &&& t.h6)

/-- Check the continuation for every support pair with at least sixteen common
sites. The arrays can represent one chunk of the labelled atlas. -/
def checkSupports (anchors images : Array SupportCube)
    (next : SupportCube → SupportCube → Bool) : Bool :=
  images.all fun t => anchors.all fun s => overlap s t < 16 || next s t

end SevenCycleRuntime.Adjacent
