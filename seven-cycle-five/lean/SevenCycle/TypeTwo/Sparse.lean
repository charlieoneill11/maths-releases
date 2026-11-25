import SevenCycle.TypeTwo.Planar
import SevenCycleRuntime.TypeTwoDomains
import SevenCycle.TypeThree.FastCuts

/-! Sparse, class-batched candidate domains for the six-projection join. -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry
open Bitsets (Cube)
open Packed (collect wanted)

private theorem keep_sparse {keys : Std.HashMap PairKey Unit} {key : PairKey} (hk : key ∈ keys)
    (m : DomainIndex) (u w : Cube)
    (h : w ∈ bucket m key ∨ Packed.key u = key ∧ u = w) : w ∈ bucket (Packed.extend keys m u) key := by
  by_cases he : Packed.key u = key
  · simp [Packed.extend, he, Std.HashMap.contains_iff_mem.mpr hk, bucket,
      Std.HashMap.getD_eq_getD_getElem?, Array.mem_push] at h ⊢
    tauto
  · obtain hm | ⟨hk',_⟩ := h
    · by_cases hb : keys.contains (Packed.key u)
      · simpa only [Packed.extend, hb, if_true, bucket, Std.HashMap.getD_alter, beq_iff_eq, he, if_false] using hm
      · simpa only [Packed.extend, hb, if_false] using hm
    · exact False.elim (he hk')

theorem collect_covers_key (images : Cube → Array Cube) (ss : Array Cube)
    (keys : Std.HashMap PairKey Unit) {r w : Cube} (hr : r ∈ ss) (hw : w ∈ images r)
    (hk : Packed.key w ∈ keys) : w ∈ bucket (collect images ss keys) (Packed.key w) := by
  apply collect_covers images (fun m t => (images t).foldl (Packed.extend keys) m)
    (fun m => w ∈ bucket m (Packed.key w)) w _ ss {} r hr hw
  intro m a h
  refine Planar.fold_keeps (images a) (Packed.extend keys) m
    (fun m => w ∈ bucket m (Packed.key w)) (fun u => u = w) ?_ ?_
  · intro tbl u h'
    exact keep_sparse hk tbl u w (h'.imp_right fun he => ⟨congrArg Packed.key he,he⟩)
  · exact h.imp_right (fun hi => ⟨w,hi,rfl⟩)

def markKeys (cs : Vector Contact 6) := cs.map fun c => (c.axis,c.start)

theorem wanted_has (s t : Cube) (cs : Vector Contact 6) (j : Fin 6) :
    anchorKey TypeThree.fastCut s t cs[j] ∈ wanted s t (markKeys cs) := by
  let k : PairKey := anchorKey TypeThree.fastCut s t cs[j]
  let put (m : Std.HashMap PairKey Unit) (u : Fin 3 × Fin 7) :=
    m.insert (TypeThree.fastCut s u.1 u.2, TypeThree.fastCut t u.1 u.2) ()
  let us := (markKeys cs).toArray
  apply Planar.fold_keeps us put {} (fun m => k ∈ m) (fun u => u = (cs[j].axis,cs[j].start))
  · intro m a h
    rcases h with hold | rfl
    · exact Std.HashMap.mem_insert.mpr (Or.inr hold)
    · exact Std.HashMap.mem_insert_self
  · refine Or.inr ⟨_, ?_, rfl⟩
    have hc : cs[j] ∈ cs.toArray := by
      exact Array.getElem_mem (xs := cs.toArray) (i := j.val) (by simpa using j.isLt)
    exact Array.mem_map_of_mem (f := fun c : Contact => (c.axis,c.start)) hc

/-- The true cube at each marked port occurs even when only these six buckets
are materialised. The hypothesis describes exactly which source classes are
needed for a batched run. -/
theorem batchDomains_cover {C : Points} {s t : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 2 t)
    (cs : Vector Contact 6) (rows : Array Cube) (keys : Std.HashMap PairKey Unit)
    (hkeys : ∀ j : Fin 6, anchorKey TypeThree.fastCut s t cs[j] ∈ keys)
    (hrow : ∀ j : Fin 6, ∃ r ∈ rows, ∃ w ∈ Bitsets.orbitImages r,
      TypeThree.RepresentsBand C cs[j].axis.succ cs[j].start w) :
    CoversJoin C 0 (cs.map contactSlot) (domainsFor TypeThree.fastCut (collect Bitsets.orbitImages rows keys) s t cs) := by
  intro j
  let c := cs[j]
  obtain ⟨r,hr,w,hw,hrep⟩ := hrow j
  have eqkey : Packed.key w = anchorKey TypeThree.fastCut s t c := by
    simp only [Packed.key, anchorKey, TypeThree.fastCut_eq]
    exact Prod.ext (crosses_transverse c.axis hs hrep).symm (crosses_transverse c.axis ht hrep).symm
  have hh := hkeys j
  have hkw : Packed.key w ∈ keys := eqkey ▸ hh
  have hget := collect_covers_key Bitsets.orbitImages rows _ hr hw hkw
  rw [eqkey] at hget
  have hslot : (cs.map contactSlot)[j] = contactSlot c := Vector.getElem_map (xs := cs) (i := j.val) ..
  have hd : (domainsFor TypeThree.fastCut (collect Bitsets.orbitImages rows keys) s t cs)[j] =
      bucket (collect Bitsets.orbitImages rows keys) (anchorKey TypeThree.fastCut s t c) :=
    Vector.getElem_map (xs := cs) (i := j.val) ..
  rw [hslot, hd]
  exact ⟨Fin.succ_ne_zero _, w, hget, stores_of_rep hrep⟩

end SevenCycle.TypeTwo
