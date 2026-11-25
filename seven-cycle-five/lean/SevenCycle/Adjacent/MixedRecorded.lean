import SevenCycle.Adjacent.RecordedFrame
import SevenCycle.Adjacent.MixedAnchor
import SevenCycle.Adjacent.MixedHistogram

/-! From actual six-band records at every adjacent axis to mixed-profile exclusion. -/

namespace SevenCycle.Adjacent.MixedCommon

open Proof Blueprint Blueprint.SearchSpec SlabJoin SlabReconstruction
open MixedSlabs (Profile)

private theorem sort_record {C : Points} {m : Frame} (valid : ValidFrame m) {k : Axis} (one : m.gap k = 1)
    (h : RecordedFrame.AtAnchor C m k) :
    AtAnchor C m (profileFor (tally m)) (rowsFor (tally m)) k ∧
      (tally m = 16 ∨ tally m = 13 ∨ tally m = 10 ∨ tally m = 9) := by
  obtain ⟨g,s,t,u,coord,hD,hbase,hs,ht,hu,record⟩ := h
  let f := FrameAction.moved g m
  let gaps := Scan.gapsOf f
  let cs := Scan.centersOf f
  have anchor := (FrameAction.anchor_fields _ _ _ coord).1
  have hgap : f.gap 0 = 1 := (congrArg m.gap anchor).trans one
  have validF : ValidFrame f := fun j => valid (g.1 j)
  obtain ⟨r,hr,he⟩ := SlabTables.leaf_sound hD s t u hs ht hu gaps cs (Scan.gaps_valid f validF) record
  obtain ⟨inRows,ordered,choices⟩ := rows_profile valid g hgap r hr
  refine ⟨atAnchor_of_local g cs (SlabTables.orderToCanonical gaps) (SlabTables.rankPerm gaps) anchor
    (SlabTables.rank_zero _) (SlabTables.order_apply _) ?_ ?_ r inRows he, choices⟩
  · intro j
    rw [← ordered]
    change f.gap j = ((SlabTables.sortedProfile gaps).get ((SlabTables.rankPerm gaps) j)).val
    rw [SlabTables.sorted_at]
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hgap
    · exact (get_gap f validF i).symm
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change 1 = f.base 0 + (f.gap 0 : Height)
      rw [hgap,show f.base 0 = 0 from hbase]
      rfl
    · exact (Scan.frame_starts f i).1

private theorem physical_two (p : Bool) : physicalFrame (MixedEnd.twoProfile p) = Stage6.frame p := by
  have g (i : Axis) : (physicalFrame (MixedEnd.twoProfile p)).gap i = (Stage6.frame p).gap i := by
    cases p <;> fin_cases i <;> rfl
  have b (i : Axis) : (physicalFrame (MixedEnd.twoProfile p)).base i = (Stage6.frame p).base i := by
    cases p <;> fin_cases i <;> rfl
  exact frame_eq g b

/-- In every mixed profile with an adjacent axis the verified anchored rows
are incompatible with the physical marked frame. -/
theorem reject {C : Points} (hc : packing cycleStep C) {m : Frame} (hm : Marked m C)
    (adjacent : ∃ k, m.gap k = 1) (mixed : ∃ l, m.gap l ≠ 1)
    (records : ∀ k, m.gap k = 1 → RecordedFrame.AtAnchor C m k) : False := by
  obtain ⟨a,ha⟩ := adjacent
  have all (k : Axis) (hk : m.gap k = 1) := sort_record hm.1 hk (records k hk)
  obtain ⟨⟨g,_,gm,gRow⟩,choices⟩ := all a ha
  have code : packing cycleStep (actOnCode g C) := by
    intro x hx y hy bad
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact hc u hu v hv ((Symmetry.act_confusable g _ _).mp bad)
  have cover := coverage g gm gRow (fun k hk => (all k hk).1)
  have marked := FrameAction.marked g hm
  rw [gm] at marked
  rcases choices with n | n | n | n
  · obtain ⟨l,hl⟩ := mixed
    let j := g.1.symm l
    have h := congrArg (fun M : Frame => M.gap j) gm
    change m.gap (g.1 j) = ((profileFor (tally m)).get j).val at h
    have allOne : ∀ i : Axis, ((profileFor 16).get i).val = 1 := by decide
    rw [n,allOne,show g.1 j=l from g.1.apply_symm_apply _] at h
    exact hl h
  · rw [n] at cover
    exact MixedEnd.three code cover
  · rw [n] at cover marked
    change Marked (physicalFrame (MixedEnd.twoProfile false)) _ at marked
    rw [physical_two] at marked
    exact MixedEnd.two false code marked cover
  · rw [n] at cover marked
    change Marked (physicalFrame (MixedEnd.twoProfile true)) _ at marked
    rw [physical_two] at marked
    exact MixedEnd.two true code marked cover

end SevenCycle.Adjacent.MixedCommon
