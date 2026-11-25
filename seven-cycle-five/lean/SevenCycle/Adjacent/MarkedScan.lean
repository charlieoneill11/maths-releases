import SevenCycle.Adjacent.Scan
import SevenCycle.Proof.FrameAction

namespace SevenCycle.Adjacent.Scan

open Proof Blueprint Bitsets SearchSpec

def gapsOf (m : Frame) : Marks := Vector.ofFn fun a : Fin 3 =>
  (m.gap a.succ : ZMod 7)

def centersOf (m : Frame) : Marks := Vector.ofFn fun a : Fin 3 => start m a.succ true

theorem gaps_valid (m : Frame) (hm : ValidFrame m) (i : Fin 3) :
    (gapsOf m).get i ∈ (#[1,2,3] : Array Contacts.Height) := by
  simp only [gapsOf, getFn]
  have h := hm i.succ
  have dis : m.gap i.succ = 1 ∨ m.gap i.succ = 2 ∨ m.gap i.succ = 3 := by omega
  rcases dis with h | h | h <;> rw [h] <;> simp only [Nat.cast_one, Nat.cast_ofNat, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem frame_starts (m : Frame) (i : Fin 3) :
    (centersOf m).get i = start m i.succ true ∧
    (centersOf m).get i - (gapsOf m).get i = start m i.succ false := by
  simp only [centersOf, gapsOf, getFn, true_and]
  change m.base i.succ + (m.gap i.succ : Height) - (m.gap i.succ : Height) = m.base i.succ
  exact add_sub_cancel_right _ _

/-- Apply the combined three-stage search to any chosen gap-one axis of
the *same* marked code. The affine equation and the induced complete frame
are retained for the subsequent slab and exterior joins. -/
theorem checked_frame (atlas : Contacts.AtlasComplete) {C : Points}
    (hc : packing cycleStep C) (m : Frame) (hm : Marked m C) (k : Axis) (hk : m.gap k = 1)
    {next : Visit} (ok : checkClasses atlasPlanes next = true) :
    ∃ g : Blueprint.Isometry 4, ∃ a : Fin atlasPlanes.size, ∃ t u : Cube,
      let D := actOnCode g C
      let f := FrameAction.moved g m
      (∀ x : Tuple 4, act g x 0 = x k - m.base k) ∧ packing cycleStep D ∧ Marked f D ∧
      f.base 0 = 0 ∧ f.gap 0 = 1 ∧
      TypeThree.RepresentsBand D 0 0 atlasPlanes[a] ∧ TypeThree.RepresentsBand D 0 1 t ∧
      cubeSet u = projectedLevel D 0 1 ∧ next atlasPlanes[a] t (gapsOf f) (centersOf f) u = true := by
  let c := start m k true
  obtain ⟨g,a,b,t,ht,ha,hd,hs,he,sub,lo,hi⟩ := normalized_support_frame atlas hc k c (hm.2.2 k hk)
  have coord (x : Tuple 4) : act g x 0 = x k - m.base k := by simpa [c,start,hk] using ha x
  let f := FrameAction.moved g m
  have mark := FrameAction.marked g hm
  have axis := (FrameAction.anchor_fields g k (m.base k) coord).1
  have gap : f.gap 0 = 1 := by simpa [f,FrameAction.moved,axis] using hk
  have full (i : Fin 3) : (centersOf f).get i ∈ fullStarts (actOnCode g C) i.succ ∧
      (centersOf f).get i - (gapsOf f).get i ∈ fullStarts (actOnCode g C) i.succ := by
    rw [(frame_starts f i).1, ← (frame_starts f i).1, (frame_starts f i).2]
    exact ⟨(frame_starts f i).1 ▸ mark.2.1 _ true,mark.2.1 _ false⟩
  obtain ⟨u,hu,leaf⟩ := checkClasses_sound atlas hd a (Array.getElem_mem b.isLt) ht
    hs.symm he.symm sub lo hi (gapsOf f) (centersOf f) (gaps_valid f mark.1) full ok
  exact ⟨g,a,t,u,coord,hd,mark,FrameAction.moved_base_zero g m k coord,gap,hs.symm,he.symm,hu,leaf⟩

end SevenCycle.Adjacent.Scan
