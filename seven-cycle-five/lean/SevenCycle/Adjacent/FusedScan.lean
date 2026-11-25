import SevenCycle.Adjacent.FusedMiddle
import SevenCycle.Adjacent.MarkedScan

namespace SevenCycle.Adjacent.ScanFused

open Proof Blueprint Bitsets SearchSpec
open Scan (Marks Visit)

def checkClasses (classes : Array Cube) (gate leaf : Visit) : Bool :=
  let idx := Contacts.index orbitImages atlasPlanes
  checkSupportClasses classes (fun s t => checkPair idx s t gate leaf)

theorem checkPair_sound (atlas : Contacts.AtlasComplete)
    {C : Points} (hc : packing cycleStep C) {s t u : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) (lo : 16 ≤ (cubeSet u).card) (hi : (cubeSet u).card ≤ 19)
    (gaps cs : Marks) (valid : ∀ a, gaps.get a ∈ (#[1,2,3] : Array Contacts.Height))
    (full : ∀ a : Fin 3, cs.get a ∈ fullStarts C a.succ ∧ cs.get a - gaps.get a ∈ fullStarts C a.succ)
    {gate leaf : Visit} (ok : checkPair (Contacts.index orbitImages atlasPlanes) s t gate leaf = true) :
    ∃ v : Cube, cubeSet v = (projectedLevel C 0 1).filter (fun x => covered gaps cs x) ∧
      (gate s t gaps cs v = true → ∃ r : Cube, cubeSet r = projectedLevel C 0 1 ∧ leaf s t gaps cs r = true) := by
  let idx := Contacts.index orbitImages atlasPlanes
  have hit {a : Fin 3} (j : Contacts.Height) (h : j ∈ fullStarts C a.succ) :
      idx.contains (Contacts.anchorKey s t a j) = true := by
    obtain ⟨w, _, entry⟩ := Contacts.contact_covers atlas hc hs ht h
    by_contra hn
    have hm : Contacts.anchorKey s t a j ∉ idx := fun e => hn (Std.HashMap.contains_iff_mem.mpr e)
    change Contacts.middle w ∈ idx.getD (Contacts.anchorKey s t a j) #[] at entry
    rw [Std.HashMap.getD_eq_fallback hm] at entry
    exact Array.not_mem_empty _ entry
  have member (a : Fin 3) : (gaps.get a, cs.get a) ∈ Scan.ordered idx s t a :=
    Scan.ordered_mem (valid a) (hit _ (full a).1) (hit _ (full a).2)
  have filled (a : Fin 3) : (Scan.ordered idx s t a).isEmpty = false :=
    Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨_,member a⟩
  change checkPair idx s t gate leaf = true at ok
  simp only [checkPair, filled, Bool.false_or] at ok
  have done_ := Array.all_eq_true'.mp (Array.all_eq_true'.mp
    (Array.all_eq_true'.mp ok _ (member 0)) _ (member 1)) _ (member 2)
  have eta (x : Marks) : #v[x.get 0,x.get 1,x.get 2] = x := by
    apply Vector.ext
    intro n hn
    have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  simp only [eta] at done_
  exact checked_sound atlas hc hs ht hu lo hi gaps cs full done_

theorem checkClasses_sound (atlas : Contacts.AtlasComplete) {C : Points}
    (hc : packing cycleStep C) {classes : Array Cube} (a : Fin atlasPlanes.size)
    {ref t : Cube} (hr : ref ∈ classes) (hgen : t ∈ orbitImages ref)
    (hs : TypeThree.RepresentsBand C 0 0 atlasPlanes[a]) (ht : TypeThree.RepresentsBand C 0 1 t)
    (sub : projectedLevel C 0 1 ⊆ cubeSet atlasPlanes[a] ∩ cubeSet t)
    (lo : 16 ≤ (projectedLevel C 0 1).card) (hi : (projectedLevel C 0 1).card ≤ 19)
    (gaps cs : Marks) (valid : ∀ i, gaps.get i ∈ (#[1,2,3] : Array Contacts.Height))
    (full : ∀ i : Fin 3, cs.get i ∈ fullStarts C i.succ ∧ cs.get i - gaps.get i ∈ fullStarts C i.succ)
    {gate leaf : Visit} (ok : checkClasses classes gate leaf = true) :
    ∃ v : Cube, cubeSet v = (projectedLevel C 0 1).filter (fun x => covered gaps cs x) ∧
      (gate atlasPlanes[a] t gaps cs v = true →
        ∃ r : Cube, cubeSet r = projectedLevel C 0 1 ∧ leaf atlasPlanes[a] t gaps cs r = true) := by
  let u := buildCube fun x => decide (x ∈ projectedLevel C 0 1)
  have hu : cubeSet u = projectedLevel C 0 1 := by ext x; simp [u]
  exact checkPair_sound atlas hc hs ht hu (hu ▸ lo) (hu ▸ hi) gaps cs valid full
    (checkSupportClasses_retains classes
      (fun s t => checkPair (Contacts.index orbitImages atlasPlanes) s t gate leaf) ok a hr hgen sub lo)

/-- The prefilter sees the physical restriction of the middle to the six
marked transverse windows. After acceptance the final check receives the
actual complete middle. Both checks use the frame induced by the same
isometry of the original marked code. -/
theorem checked_frame (atlas : Contacts.AtlasComplete) {C : Points}
    (hc : packing cycleStep C) (m : Frame) (hm : Marked m C) (k : Axis) (hk : m.gap k = 1)
    {gate leaf : Visit} (ok : checkClasses atlasPlanes gate leaf = true) :
    ∃ g : Blueprint.Isometry 4, ∃ a : Fin atlasPlanes.size, ∃ t v : Cube,
      let D := actOnCode g C
      let f := FrameAction.moved g m
      let gaps := Scan.gapsOf f
      let cs := Scan.centersOf f
      (∀ x : Tuple 4, act g x 0 = x k - m.base k) ∧ packing cycleStep D ∧ Marked f D ∧
      f.base 0 = 0 ∧ f.gap 0 = 1 ∧
      TypeThree.RepresentsBand D 0 0 atlasPlanes[a] ∧ TypeThree.RepresentsBand D 0 1 t ∧
      cubeSet v = (projectedLevel D 0 1).filter (fun x => covered gaps cs x) ∧
      (gate atlasPlanes[a] t gaps cs v = true →
        ∃ u : Cube, cubeSet u = projectedLevel D 0 1 ∧ leaf atlasPlanes[a] t gaps cs u = true) := by
  let c := start m k true
  obtain ⟨g,a,b,t,ht,ha,hd,hs,he,sub,lo,hi⟩ := normalized_support_frame atlas hc k c (hm.2.2 k hk)
  have coord (x : Tuple 4) : act g x 0 = x k - m.base k := by simpa [c,start,hk] using ha x
  let f := FrameAction.moved g m
  have mark := FrameAction.marked g hm
  have axis := (FrameAction.anchor_fields g k (m.base k) coord).1
  have gap : f.gap 0 = 1 := by simpa [f,FrameAction.moved,axis] using hk
  have full (i : Fin 3) : (Scan.centersOf f).get i ∈ fullStarts (actOnCode g C) i.succ ∧
      (Scan.centersOf f).get i - (Scan.gapsOf f).get i ∈ fullStarts (actOnCode g C) i.succ := by
    constructor
    · rw [(Scan.frame_starts f i).1]; exact mark.2.1 _ true
    · rw [(Scan.frame_starts f i).2]; exact mark.2.1 _ false
  obtain ⟨v,hv,go⟩ := checkClasses_sound atlas hd a (Array.getElem_mem b.isLt) ht
    hs.symm he.symm sub lo hi (Scan.gapsOf f) (Scan.centersOf f) (Scan.gaps_valid f mark.1) full ok
  exact ⟨g,a,t,v,coord,hd,mark,FrameAction.moved_base_zero g m k coord,gap,hs.symm,he.symm,hv,go⟩

end SevenCycle.Adjacent.ScanFused
