import SevenCycleRuntime.BandStage
import SevenCycle.Adjacent.FusedScan
import SevenCycle.Adjacent.SlabTables

namespace SevenCycle.Adjacent.FrontSearch
open Bitsets

def gate (needed : BandJoin.Prefix → Bool) : Scan.Visit :=
  let idx := BandJoin.indexPrefixes orbitImages needed atlasPlanes
  BandStage.survives needed idx

/-- Stage 1 enumerates every anchor against the selected interval of target
classes. The six-band gate acts on the visible middle; the terminal uses
the full physical middle selected by the subsequent completion. -/
def range (needed : BandJoin.Prefix → Bool) (lo hi : Nat) : Bool :=
  let idx := BandJoin.indexPrefixes orbitImages needed atlasPlanes
  ScanFused.checkClasses (atlasPlanes.extract lo hi) (BandStage.survives needed idx) SlabTables.leaf

private theorem cover {α : Type} (rows : Array α) (pred : α → Bool)
    (wins : ∀ i : Fin rows.size, ∃ lo hi : Nat, lo ≤ i.val ∧ i.val < hi ∧
      (rows.extract lo hi).all pred = true) : rows.all pred = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro target hm
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp hm
  obtain ⟨lo,top,hlo,hhi,pass⟩ := wins ⟨i,hi⟩
  have mem : rows[i] ∈ rows.extract lo top := by
    apply Array.mem_extract_iff_getElem.mpr
    have bound : i < min top rows.size := lt_min hhi hi
    refine ⟨i-lo,Nat.sub_lt_sub_right hlo bound,?_⟩
    simp only [Nat.add_sub_of_le hlo]
  exact Array.all_eq_true_iff_forall_mem.mp pass _ mem

/-- Arbitrary adjacent target intervals may be used. Coverage of the class
indices connects the separately checked intervals to the full front search. -/
theorem of_ranges (needed : BandJoin.Prefix → Bool)
    (wins : ∀ i : Fin atlasPlanes.size, ∃ lo hi : Nat, lo ≤ i.val ∧ i.val < hi ∧ range needed lo hi = true) :
    ScanFused.checkClasses atlasPlanes (gate needed) SlabTables.leaf = true := by
  apply cover atlasPlanes
  exact wins

end SevenCycle.Adjacent.FrontSearch
