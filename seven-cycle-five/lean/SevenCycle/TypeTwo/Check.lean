import SevenCycle.TypeTwo.Sparse

/-! ## Executable exclusion of a fixed type-two support pair and placement -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec
open Bitsets (Cube)

def siteWord (i : Fin 343) : Tuple 3 :=
  ![((i.val / 49 : Nat) : Height), ((i.val / 7 % 7 : Nat) : Height), ((i.val % 7 : Nat) : Height)]

def sites (r : Cube) : Array (Fin 343) :=
  (Array.finRange 343).filter fun i => Bitsets.cubeMem r (siteWord i)

def endpoint (points : Array (Fin 343)) (i : Nat) : Tuple 4 :=
  Fin.cons 0 (siteWord (points[i]?.getD 0))

structure LayoutCheck where
  left : Cube
  right : Cube
  contacts : Vector Contact 6


/-- For the final join the sites on each side may be in any order. Its full
conflict matrix checks all 33 × 33 cross-pairs. -/
def checkIn (idx : DomainIndex) (data : LayoutCheck) : Bool :=
  let L := sites data.left
  let R := sites data.right
  L.size == 33 && R.size == 33 &&
    rejectsJoin (data.contacts.map contactSlot) (fun i => (endpoint L i, endpoint R i))
      0 1 2 (domainsFor TypeThree.fastCut idx data.left data.right data.contacts)

private theorem endpoint_mem {r : Cube} {C : Points} {h : Height}
    (hs : TypeThree.RepresentsBand C 0 h r) (hn : (sites r).size = 33) (i : Nat) (hi : i < 33) :
    endpoint (sites r) i ∈ stripe C 0 h := by
  apply (stores_of_rep hs _ (by simp [endpoint])).mp
  have hlt : i < (sites r).size := hn ▸ hi
  have hm : (sites r)[i] ∈ sites r := Array.getElem_mem hlt
  have he : Bitsets.cubeMem r (siteWord (sites r)[i]) := (Array.mem_filter.mp hm).2
  simpa only [endpoint, Array.getElem?_eq_getElem hlt, Option.getD_some, dropCoord,
    Fin.zero_succAbove, Fin.cons_succ] using he

def gatherKeys (layouts : Array LayoutCheck) : Std.HashMap PairKey Unit :=
  layouts.foldl (init := {}) fun ks l =>
    (Packed.wanted l.left l.right (markKeys l.contacts)).keysArray.foldl (fun m k => m.insert k ()) ks

/-- All requested layouts share one pass over all the chosen atlas orbits. -/
def checkBatch (classes : Array Cube) (layouts : Array LayoutCheck) : Bool :=
  let idx := Packed.collect Bitsets.orbitImages classes (gatherKeys layouts)
  layouts.all (checkIn idx)

theorem keys_cover {l : LayoutCheck} {layouts : Array LayoutCheck} (hl : l ∈ layouts)
    (j : Fin 6) : anchorKey TypeThree.fastCut l.left l.right l.contacts[j] ∈ gatherKeys layouts := by
  let k := anchorKey TypeThree.fastCut l.left l.right l.contacts[j]
  let add (ks : Std.HashMap PairKey Unit) (s : LayoutCheck) :=
    (Packed.wanted s.left s.right (markKeys s.contacts)).keysArray.foldl (fun m u => m.insert u ()) ks
  apply Planar.fold_keeps layouts add {} (fun m => k ∈ m) (fun t => t = l) _
    (Or.inr ⟨l,hl,rfl⟩)
  intro m a h
  let keys := Packed.wanted a.left a.right (markKeys a.contacts)
  apply Planar.fold_keeps keys.keysArray (fun (v : Std.HashMap PairKey Unit) u => v.insert u ()) m
    (fun v => k ∈ v) (fun u => u = k)
  · intro v u h'
    rcases h' with hh | rfl
    · exact Std.HashMap.mem_insert.mpr (Or.inr hh)
    · exact Std.HashMap.mem_insert_self
  · rcases h with hh | rfl
    · exact Or.inl hh
    · exact Or.inr ⟨k,Std.HashMap.mem_keysArray.mpr (wanted_has _ _ _ j),rfl⟩

/-- A single physical join excludes a code whenever its six true projections are present. -/
theorem checkIn_sound (idx : DomainIndex) (data : LayoutCheck) (h : checkIn idx data)
    {C : Points} {m : Frame} (hm : Marked m C) (hbase : m.base 0 = 0) (hgap : m.gap 0 = 2)
    (hS : TypeThree.RepresentsBand C 0 0 data.left) (hT : TypeThree.RepresentsBand C 0 2 data.right)
    (hbound : CoversJoin C 0 (data.contacts.map contactSlot)
      (domainsFor TypeThree.fastCut idx data.left data.right data.contacts)) :
    ¬ packing cycleStep C := by
  unfold checkIn at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hL,hR⟩,hjoin⟩ := h
  have h1 : m.base 0 + 1 = 1 := by simp [hbase]
  have h2 : start m 0 true = 2 := by simp [start, hbase, hgap]
  have hepts (i : ℕ) (hi : i < 33) :
      (endpoint (sites data.left) i) ∈ projections m C 0 false ∧
      endpoint (sites data.right) i ∈ projections m C 0 true := by
    constructor
    · simpa [projections, start, hbase] using endpoint_mem hS hL i hi
    · simpa only [projections,h2] using endpoint_mem hT hR i hi
  apply rejectsJoin_excludes_code_of_endpoints hm hgap
    (fun i => (endpoint (sites data.left) i, endpoint (sites data.right) i)) hepts _ _ hbound
  simpa only [h1,h2] using hjoin

/-- A checked batch excludes a code inducing any of its layouts when the
batch's source classes cover that layout's true six transverse projections. -/
theorem checkBatch_sound (classes : Array Cube) (layouts : Array LayoutCheck) (data : LayoutCheck)
    (hmdata : data ∈ layouts) (hcheck : checkBatch classes layouts = true)
    {C : Points} {m : Frame} (hm : Marked m C) (hbase : m.base 0 = 0) (hgap : m.gap 0 = 2)
    (hS : TypeThree.RepresentsBand C 0 0 data.left) (hT : TypeThree.RepresentsBand C 0 2 data.right)
    (hcover : ∀ j : Fin 6, ∃ r ∈ classes, ∃ w ∈ Bitsets.orbitImages r,
      TypeThree.RepresentsBand C data.contacts[j].axis.succ data.contacts[j].start w) :
    ¬ packing cycleStep C := by
  let keys := gatherKeys layouts
  let idx := Packed.collect Bitsets.orbitImages classes keys
  have h : checkIn idx data := Array.all_eq_true_iff_forall_mem.mp hcheck data hmdata
  exact checkIn_sound idx data h hm hbase hgap hS hT
    (batchDomains_cover hS hT data.contacts classes keys (keys_cover hmdata) hcover)

/-- Atlas completeness discharges the class hypothesis in a full-domain run. -/
theorem checked_full_batch (atlas : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 33 →
      ∃ q : Fin atlasPlanes.size, ∃ g : Isometry 3, D = actOnCode g (atlasRepresentative q))
    (layouts : Array LayoutCheck) (data : LayoutCheck) (hl : data ∈ layouts)
    (hc : checkBatch atlasPlanes layouts = true)
    {C : Points} {m : Frame} (hm : Marked m C) (hbase : m.base 0 = 0) (hgap : m.gap 0 = 2)
    (hs : TypeThree.RepresentsBand C 0 0 data.left) (ht : TypeThree.RepresentsBand C 0 2 data.right)
    (hmarks : ∀ j : Fin 6, data.contacts[j].start ∈ fullStarts C data.contacts[j].axis.succ) :
    ¬ packing cycleStep C := by
  intro hC
  refine checkBatch_sound atlasPlanes layouts data hl hc hm hbase hgap hs ht (fun j => ?_) hC
  let c := data.contacts[j]
  obtain ⟨hinj,hpack⟩ := Bands.band_projection hC c.axis.succ c.start
  have hn : (projectedBand C c.axis.succ c.start).card = 33 :=
    (Finset.card_image_of_injOn hinj).trans (Finset.mem_filter.mp (hmarks j)).2
  obtain ⟨q,g,hg⟩ := atlas _ hpack hn
  obtain ⟨w,hw,hspec⟩ := Bitsets.orbitImages_complete g atlasPlanes[q]
  have hq : atlasPlanes[q] ∈ atlasPlanes := Array.getElem_mem (xs := atlasPlanes) q.isLt
  exact ⟨atlasPlanes[q],hq,w,hw,hspec.trans hg.symm⟩

end SevenCycle.TypeTwo
