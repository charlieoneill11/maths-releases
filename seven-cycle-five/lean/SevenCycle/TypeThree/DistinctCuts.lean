import SevenCycle.Proof.Bitsets

/-! # An invariant of the gap-three planar filter

When two specified anchor cuts agree, a transverse witness would have two equal
cuts at distance three. Checking that this never happens uses the released
representatives one row at a time. Only the row membership of a particular
candidate is needed in the soundness theorem. -/

namespace SevenCycle.TypeThree
open SevenCycle.Bitsets

private def residue (t : Fin 7) : ZMod 7 := t

def occupies (r : Cube) (k : Fin 3) (t : ZMod 7) (p : Proof.Tuple 2) : Bool :=
  cubeMem r (k.insertNth (α := fun _ => ZMod 7) t p) ||
    cubeMem r (k.insertNth (α := fun _ => ZMod 7) (t+1) p)

theorem mem_cut_iff (r : Cube) (k : Fin 3) (t : ZMod 7) (p : Proof.Tuple 2) :
    p ∈ planeSet (cut r k t) ↔ occupies r k t p := by
  simp [cut, planeSet_or, lev, occupies]

def cutsDistinct (rows : Array Cube) : Bool :=
  rows.all fun r => (Array.ofFn (id : Fin 3 → Fin 3)).all fun k =>
    (Array.ofFn (id : Fin 7 → Fin 7)).all fun t =>
      (Array.ofFn (id : Fin 49 → Fin 49)).any fun i =>
        let p := pointAt i
        occupies r k (residue t) p != occupies r k (residue t + 3) p

theorem cutsDistinct_sound {rows : Array Cube} (h : cutsDistinct rows = true)
    {r : Cube} (hr : r ∈ rows) (k : Fin 3) (t : ZMod 7) :
    planeSet (cut r k t) ≠ planeSet (cut r k (t+3)) := by
  have hk := Array.all_eq_true_iff_forall_mem.mp
    (Array.all_eq_true_iff_forall_mem.mp h r hr) k (Array.mem_ofFn.mpr ⟨k, rfl⟩)
  have ht := Array.all_eq_true_iff_forall_mem.mp hk t (Array.mem_ofFn.mpr ⟨t, rfl⟩)
  obtain ⟨i, _, hdiff⟩ := Array.any_eq_true'.mp ht
  let p := pointAt i
  have ne : occupies r k t p ≠ occupies r k (t+3) p := bne_iff_ne.mp hdiff
  intro e
  apply ne
  apply Bool.eq_iff_iff.mpr
  rw [← mem_cut_iff, ← mem_cut_iff, e]

end SevenCycle.TypeThree
