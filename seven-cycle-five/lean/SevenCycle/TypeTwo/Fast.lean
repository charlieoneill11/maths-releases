import SevenCycle.TypeTwo.Cross

namespace SevenCycle.TypeTwo.Search

open Proof Blueprint Blueprint.SearchSpec
open Bitsets (Cube)

attribute [local irreducible] atlasPlanes

def fastCheckIn (idx : DomainIndex) (l : LayoutCheck) : Bool :=
  Cross.reject (markKeys l.contacts) (domainsFor TypeThree.fastCut idx l.left l.right l.contacts) ||
    checkIn idx l

def fastBatch (classes : Array Cube) (layouts : Array LayoutCheck) : Bool :=
  let idx := Packed.collect Bitsets.orbitImages classes (gatherKeys layouts)
  layouts.all (fastCheckIn idx)

/-- The first check only tests pairs of transverse crossing masks. Layouts
passing it are tested by the physical conflict matrix on the same six domains. -/
def fastCheck (classes sources targets : Array Cube) : Bool :=
  fastBatch classes ((scan Bitsets.orbitImages classes sources targets).map layoutCheck)

private theorem full_domains {C : Points} {s t : Cube} (atlas : AtlasCovers)
    (hc : packing cycleStep C) (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 2 t)
    (cs : Vector Contact 6) (keys : Std.HashMap PairKey Unit)
    (hkeys : ∀ j : Fin 6, anchorKey TypeThree.fastCut s t cs[j] ∈ keys)
    (hfull : ∀ j : Fin 6, cs[j].start ∈ fullStarts C cs[j].axis.succ) :
    Cross.Covers C (markKeys cs) (domainsFor TypeThree.fastCut
      (Packed.collect Bitsets.orbitImages atlasPlanes keys) s t cs) := by
  intro j
  let c := cs[j]
  obtain ⟨q,w,hw,hrep⟩ := full_projection atlas hc (hfull j)
  have he : Packed.key w = anchorKey TypeThree.fastCut s t c := by
    simp only [Packed.key,anchorKey,TypeThree.fastCut_eq]
    exact Prod.ext (crosses_transverse c.axis hs hrep).symm (crosses_transverse c.axis ht hrep).symm
  have hget := collect_covers_key Bitsets.orbitImages atlasPlanes keys
    (Array.getElem_mem (xs := atlasPlanes) q.isLt) hw (he ▸ hkeys j)
  rw [he] at hget
  have hslot : (markKeys cs)[j] = (c.axis,c.start) := Vector.getElem_map (xs := cs) (i := j.val) ..
  have hd : (domainsFor TypeThree.fastCut (Packed.collect Bitsets.orbitImages atlasPlanes keys) s t cs)[j] =
      bucket (Packed.collect Bitsets.orbitImages atlasPlanes keys) (anchorKey TypeThree.fastCut s t c) :=
    Vector.getElem_map (xs := cs) (i := j.val) ..
  erw [hslot, hd]
  exact ⟨w,hget,hrep⟩

theorem fastCheck_sound (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33) (atlas : AtlasCovers)
    {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (hb : m.base 0 = 0) (hg : m.gap 0 = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    (ss ts : Array Cube) (i : Fin ss.size) {t r : Cube} (hr : r ∈ ts) (hw : t ∈ Bitsets.orbitImages r)
    (hs : TypeThree.RepresentsBand C 0 0 ss[i]) (ht : TypeThree.RepresentsBand C 0 2 t)
    (hcheck : fastCheck atlasPlanes ss ts) : False := by
  let p := framePlacement m
  let l := layoutCheck ⟨ss[i],t,p⟩
  let layouts := (scan Bitsets.orbitImages atlasPlanes ss ts).map layoutCheck
  have hl : l ∈ layouts := Array.mem_map_of_mem (f := layoutCheck) (scan_retains h3 atlas hc hm hb hg h113 hn ss ts i hr hw hs ht)
  let keys := gatherKeys layouts
  let idx := Packed.collect Bitsets.orbitImages atlasPlanes keys
  have checked : fastCheckIn idx l := Array.all_eq_true_iff_forall_mem.mp hcheck _ hl
  have hmarks (j : Fin 6) : l.contacts[j].start ∈ fullStarts C l.contacts[j].axis.succ := by
    have hh : l.contacts[j] = (⟨((Mid.contacts p)[j]).1,((Mid.contacts p)[j]).2⟩ : Contact) :=
      Vector.getElem_map (xs := Mid.contacts p) (i := j.val) ..
    rw [hh]
    exact frame_full hm hn _ (Array.getElem_mem (xs := (Mid.contacts p).toArray) (i := j.val) (by simp))
  have H := full_domains atlas hc hs ht l.contacts keys (keys_cover hl) hmarks
  rcases Bool.or_eq_true_iff.mp checked with cross | phys
  · exact Bool.noConfusion (cross.symm.trans (Cross.reject_false _ _ H))
  · apply checkIn_sound idx l phys hm hb hg hs ht _ hc
    apply batchDomains_cover hs ht l.contacts atlasPlanes keys (keys_cover hl)
    intro j
    obtain ⟨q,w,hw,hspec⟩ := full_projection atlas hc (hmarks j)
    exact ⟨_,Array.getElem_mem q.isLt,w,hw,hspec⟩

def chunk (id : Nat) : Bool :=
  if id = 0 then
    check atlasPlanes atlasPlanes (atlasPlanes.extract 0 1) &&
    check atlasPlanes atlasPlanes (atlasPlanes.extract 1 2) &&
    fastCheck atlasPlanes atlasPlanes (atlasPlanes.extract 2 16)
  else fastCheck atlasPlanes atlasPlanes (atlasPlanes.extract (id*16) ((id+1)*16))

private theorem in_extract {α : Type} {xs : Array α} {start stop : ℕ} {q : Fin xs.size}
    (hlo : start ≤ q.val) (hhi : q.val < stop) : xs[q] ∈ xs.extract start stop := by
  apply Array.mem_extract_iff_getElem.mpr
  have hq := q.isLt
  refine ⟨q.val-start, by omega, ?_⟩
  simp only [Nat.add_sub_of_le hlo]
  rfl

theorem chunk_sound (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33) (atlas : AtlasCovers)
    {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (hb : m.base 0 = 0) (hg : m.gap 0 = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    (i q : Fin atlasPlanes.size) {t : Cube} (hw : t ∈ Bitsets.orbitImages atlasPlanes[q])
    (hs : TypeThree.RepresentsBand C 0 0 atlasPlanes[i]) (ht : TypeThree.RepresentsBand C 0 2 t)
    (id : Nat) (hlo : id*16 ≤ q.val) (hhi : q.val < (id+1)*16) (hcheck : chunk id) : False := by
  by_cases hz : id = 0
  · subst id
    obtain ⟨⟨h₀,h₁⟩,hf⟩ := (Bool.and_eq_true_iff.mp hcheck).imp_left Bool.and_eq_true_iff.mp
    by_cases h0 : q.val = 0
    · exact check_sound h3 atlas hc hm hb hg h113 hn _ _ i (in_extract (by omega) (by omega)) hw hs ht h₀
    by_cases h1 : q.val = 1
    · exact check_sound h3 atlas hc hm hb hg h113 hn _ _ i (in_extract (by omega) (by omega)) hw hs ht h₁
    exact fastCheck_sound h3 atlas hc hm hb hg h113 hn _ _ i (in_extract (by omega) (by omega)) hw hs ht hf
  · simp only [chunk, hz, if_false] at hcheck
    exact fastCheck_sound h3 atlas hc hm hb hg h113 hn _ _ i (in_extract hlo hhi) hw hs ht hcheck

end SevenCycle.TypeTwo.Search
