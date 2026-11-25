import SevenCycleRuntime.SlabTables
import SevenCycle.Adjacent.SlabReconstruction
import SevenCycle.Adjacent.MixedSlabData
import SevenCycle.Adjacent.SlabData

namespace SevenCycle.Adjacent.SlabTables
open Proof Blueprint SlabJoin SlabReconstruction

def rows (g : Gaps) : Array String :=
  sourceRows SlabData.rows MixedSlabData.rows1112 MixedSlabData.rows1122 MixedSlabData.rows1123 g

def tables := indices SlabData.rows MixedSlabData.rows1112 MixedSlabData.rows1122 MixedSlabData.rows1123

/-- Final continuation for the six-band join across all ordered profiles. -/
def leaf (s t : Contacts.Cube) (gaps cs : Gaps) (u : Contacts.Cube) : Bool :=
  recorded (tables.get (indexOf gaps)) s t cs u

private theorem gapAt_index {g : Gaps} (valid : ∀ i : Fin 3, g.get i ∈ (#[1,2,3] : Array (Fin 7))) :
    gapAt (indexOf g) = g := by
  have all : ∀ a b c : Fin 7, a ∈ (#[1,2,3] : Array (Fin 7)) → b ∈ (#[1,2,3] : Array (Fin 7)) →
    c ∈ (#[1,2,3] : Array (Fin 7)) → gapAt (indexOf #v[a,b,c]) = #v[a,b,c] := by decide +kernel
  have e : #v[g.get 0,g.get 1,g.get 2] = g := by
    apply Vector.ext
    intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl|rfl|rfl <;> rfl
  rw [← e]
  exact all _ _ _ (valid 0) (valid 1) (valid 2)

theorem leaf_sound {C : Finset (Tuple 4)} (hc : packing cycleStep C) (s t u : Bitsets.Cube)
    (hs : Bitsets.cubeSet s = projectedBand C 0 0) (ht : Bitsets.cubeSet t = projectedBand C 0 1)
    (hu : Bitsets.cubeSet u = projectedLevel C 0 1) (g cs : Gaps)
    (valid : ∀ i : Fin 3, g.get i ∈ (#[1,2,3] : Array (Fin 7))) (h : leaf s t g cs u = true) :
    ∃ r ∈ rows g, (normSlab C).image (center cs) = (rowPoints r).image (signedAction (orderToCanonical g) 0) := by
  have idx : tables.get (indexOf g) = permutedIndex (rows g) (orderToCanonical g) := by
    have get {α : Type} (f : Fin 27 → α) (i : Fin 27) : (Vector.ofFn f).get i = f i := by
      change (Vector.ofFn f)[i.val] = f i
      rw [Vector.getElem_ofFn]
    unfold tables indices
    rw [get,gapAt_index valid]
    rfl
  simp only [leaf,idx,recorded,permutedIndex,Std.HashSet.ofArray_eq_ofList,
    Std.HashSet.contains_ofList,List.contains_iff_mem,Array.mem_toList_iff,Array.mem_map] at h
  obtain ⟨r,hr,eq⟩ := h
  have mem := moved_stores r (orderToCanonical g) 0
  have bits : movedMask (oneBitMap (orderToCanonical g) 0) (readSlab r) = centeredMask s t u cs := congrArg FrameMask.bits eq
  rw [bits] at mem
  have ref := centeredMask_stores C hc s t u hs ht hu cs
  refine ⟨r,hr,?_⟩
  ext x
  obtain ⟨hj,e⟩ := UnionMasks.components x
  simpa only [e,hj,true_and] using (ref (address x)).symm.trans (mem (address x))

end SevenCycle.Adjacent.SlabTables
