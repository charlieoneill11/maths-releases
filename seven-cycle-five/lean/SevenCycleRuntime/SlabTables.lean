import SevenCycleRuntime.SlabReconstruction

namespace SevenCycle.Adjacent.SlabTables
open SlabJoin SlabReconstruction

abbrev Gaps := Vector (Fin 7) 3

def orderToCanonical (gaps : Gaps) : AxisOrder :=
  let rank := fun i : Fin 3 => (Array.finRange 3).foldl (init := 1) fun n j =>
    if gaps.get j < gaps.get i || (gaps.get j == gaps.get i && j < i) then n+1 else n
  Vector.ofFn fun k => if k.val == 0 then 0 else
    Fin.ofNat 4 (rank (Fin.ofNat 3 (k.val-1)))

/-- The transverse distances range from 1 to 3. Their histogram selects the
four nonempty input tables. -/
def sourceRows (r1111 r1112 r1122 r1123 : Array String) (gaps : Gaps) : Array String :=
  let weight := fun h : Fin 7 => if h == 1 then 4 else if h == 2 then 1 else 0
  match weight (gaps.get 0) + weight (gaps.get 1) + weight (gaps.get 2) with
  | 12 => r1111 | 9 => r1112 | 6 => r1122 | 5 => r1123 | _ => #[]

def gapAt (n : Fin 27) : Gaps := #v[
  Fin.ofNat 7 (n.val/9+1),Fin.ofNat 7 (n.val/3%3+1),Fin.ofNat 7 (n.val%3+1)]

def indexOf (g : Gaps) : Fin 27 :=
  Fin.ofNat 27 (9*((g.get 0).val-1) + 3*((g.get 1).val-1) + (g.get 2).val-1)

def permutedIndex (rows : Array String) (o : AxisOrder) : Std.HashSet FrameMask :=
  let map := oneBitMap o 0
  Std.HashSet.ofArray (rows.map fun r => FrameMask.mk (movedMask map (readSlab r)))

def indices (r1111 r1112 r1122 r1123 : Array String) : Vector (Std.HashSet FrameMask) 27 :=
  Vector.ofFn fun i => let g := gapAt i
    permutedIndex (sourceRows r1111 r1112 r1122 r1123 g) (orderToCanonical g)

end SevenCycle.Adjacent.SlabTables
