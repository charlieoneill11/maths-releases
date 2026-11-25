import SevenCycleRuntime.Adjacent
import SevenCycleRuntime.TypeThree

/-! Machine-word evaluation of the two transverse prefix deficit sums. -/

namespace SevenCycleRuntime.AtlasPrune

abbrev RowBounds := Vector (Vector Nat 16384) 7
abbrev FullTable := Std.HashMap UInt64 (Array UInt64)

@[inline] def prefixBound (layers : RowBounds) (j : Fin 7) (p : UInt64) : Nat :=
  let a := (p >>> (7*(0 : Fin 7).val).toUInt64).toNat % 128
  let b := (p >>> (7*j.val).toUInt64).toNat % 128
  let idx : Fin 16384 := ⟨128*a + b, by
    have : a < 128 := Nat.mod_lt _ (by decide)
    have : b < 128 := Nat.mod_lt _ (by decide)
    omega⟩
  let n : Fin 7 := ⟨6-j.val, by omega⟩
  let bound := layers[n.val][idx.val]
  if bound = 0 then 0 else SevenCycleRuntime.Adjacent.maskCard p + (bound-1)

@[inline] private def window (table : FullTable) (layers : RowBounds) (j : Fin 7)
    (c : Vector UInt64 7) (k : Fin 3) (s : Fin 7) : Nat :=
  let m := SevenCycle.TypeThree.fastCut c k s
  max (if table.contains m then 0 else 1) (10-prefixBound layers j m)

@[inline] private def axis (table : FullTable) (layers : RowBounds) (j : Fin 7)
    (c : Vector UInt64 7) (k : Fin 3) : Nat :=
  let f := window table layers j c k
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + f 6)))))

def check (table : FullTable) (layers : RowBounds) (budget : Nat) (j : Fin 7)
    (stack : Array UInt64) : Bool :=
  let c : Vector UInt64 7 := Vector.ofFn fun i => stack[i.val]?.getD 0
  decide (axis table layers j c 1 ≤ budget) && decide (axis table layers j c 2 ≤ budget)

end SevenCycleRuntime.AtlasPrune
