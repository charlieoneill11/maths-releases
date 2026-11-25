import SevenCycle.Adjacent.CommonFrame
import SevenCycle.Adjacent.MarkedScan
import SevenCycle.Adjacent.SlabTables

namespace SevenCycle.Adjacent.RecordedFrame

open Proof Blueprint SearchSpec SlabReconstruction SlabJoin

/-- A normalized anchor returned by the complete scan. Its middle cube is the
entire physical middle layer, including sites outside the six marked windows. -/
def AtAnchor (C : Points) (m : Frame) (k : Axis) : Prop :=
  ∃ g : Isometry 4, ∃ s t u : Bitsets.Cube,
    let D := actOnCode g C
    let f := FrameAction.moved g m
    (∀ x : Tuple 4, act g x 0 = x k - m.base k) ∧ packing cycleStep D ∧ f.base 0 = 0 ∧
    Bitsets.cubeSet s = projectedBand D 0 0 ∧ Bitsets.cubeSet t = projectedBand D 0 1 ∧
    Bitsets.cubeSet u = projectedLevel D 0 1 ∧
    SlabTables.leaf s t (Scan.gapsOf f) (Scan.centersOf f) u = true

private theorem center_moves (g : Isometry 4) (m : Frame) (one : ∀ j, m.gap j = 1)
    (base : (FrameAction.moved g m).base 0 = 0) :
    CommonFrame.View g (Scan.centersOf (FrameAction.moved g m)) (fun i => start m i true) =
      fun _ => 0 := by
  let f := FrameAction.moved g m
  have trueVal (i : Axis) : act g (fun j => start m j true) i = start f i true :=
    (FrameAction.moved_centre g m i (one _)).symm
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change act g (fun j => start m j true) 0 - 1 = 0
    rw [trueVal]
    have gap : f.gap 0 = 1 := one _
    simp [start,show f.base 0 = 0 from base,gap]
  · change act g (fun j => start m j true) j.succ - (show ZMod 7 from (Scan.centersOf f).get j) = 0
    rw [trueVal,(Scan.frame_starts f j).1,sub_self]

/-- Closing every gap-one anchor against the numerically checked source
table proves the size bound in the actual original coordinate frame. -/
theorem bound1111 (C : Points) (hc : packing cycleStep C) (m : Frame)
    (one : ∀ j, m.gap j = 1) (w : ∀ k, AtAnchor C m k) : C.card ≤ 112 := by
  have aligned (k : Axis) : ∃ g : Isometry 4, ∃ cs : Centers, g.1 0 = k ∧
      CommonFrame.View g cs (fun i => start m i true) = (fun _ => 0) ∧
      ∃ r ∈ SlabData.rows, (normSlab (actOnCode g C)).image (center cs) = rowPoints r := by
    obtain ⟨g,s,t,u,coord,hD,hbase,hs,ht,hu,record⟩ := w k
    let f := FrameAction.moved g m
    have all1 : Scan.gapsOf f = #v[1,1,1] := by
      apply Vector.ext
      intro i hi
      simp only [Scan.gapsOf,Vector.getElem_ofFn,f, FrameAction.moved,one,Nat.cast_one]
      have cases : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases cases with rfl|rfl|rfl <;> rfl
    have valid (i : Fin 3) : (Scan.gapsOf f).get i ∈ (#[1,2,3] : Array (Fin 7)) := by
      apply Scan.gaps_valid f _ i
      intro j
      have gap : f.gap j = 1 := one _
      omega
    obtain ⟨r,hr,eq⟩ := SlabTables.leaf_sound hD s t u hs ht hu (Scan.gapsOf f)
      (Scan.centersOf f) valid record
    have indices : SlabTables.orderToCanonical #v[1,1,1] = identityOrder := by decide
    have chosen : SlabTables.rows #v[1,1,1] = SlabData.rows := rfl
    rw [all1,chosen] at hr
    rw [all1,indices] at eq
    have iden : signedAction identityOrder 0 = id := by funext x j; fin_cases j <;> rfl
    rw [iden,Finset.image_id] at eq
    exact ⟨g,_,(FrameAction.anchor_fields _ _ _ coord).1,center_moves g m one hbase,r,hr,eq⟩
  choose g cs a b r hr he using aligned
  exact CommonFrame.card_le_of_record C hc _ g cs a b (fun k => ⟨r k,hr k,he k⟩)

end SevenCycle.Adjacent.RecordedFrame
