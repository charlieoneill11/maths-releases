import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.RecordedFrame
import SevenCycle.Adjacent.BandStage

namespace SevenCycle.Adjacent.FrontSearch

open Proof Blueprint SearchSpec Bitsets

/-- The actual six-band gate accepts the visible middle induced by a marked
packing. Hence the fused search passes the complete physical middle to its
source-table checker in the normalized frame of any chosen gap-one axis. -/
theorem anchor_of_run (atlas : Contacts.AtlasComplete) (needed : BandJoin.Prefix → Bool)
    (checked : ScanFused.checkClasses atlasPlanes (gate needed) SlabTables.leaf = true)
    (C : Points) (hc : packing cycleStep C) (m : Frame) (hm : Marked m C) (k : Axis) (hk : m.gap k = 1) :
    RecordedFrame.AtAnchor C m k := by
  obtain ⟨g,a,t,v,coord,hD,mark,hbase,hgap,hs,ht,hvis,hnext⟩ :=
    ScanFused.checked_frame atlas hc m hm k hk checked
  let D := actOnCode g C
  let U := projectedLevel D 0 1
  let u := buildCube fun x => decide (x ∈ U)
  have hu : cubeSet u = U := by ext x; simp [u]
  have stay := BandStage.survives_sound atlas needed (visible := v) hD mark hbase hgap hs ht hu
    (by rw [hu]; exact hvis)
  obtain ⟨w,hw,hrec⟩ := hnext stay
  exact ⟨g,atlasPlanes[a],t,w,coord,hD,hbase,hs,ht,hw,hrec⟩

theorem bound1111_of_run (atlas : Contacts.AtlasComplete) (needed : BandJoin.Prefix → Bool)
    (checked : ScanFused.checkClasses atlasPlanes (gate needed) SlabTables.leaf = true)
    (C : Points) (hc : packing cycleStep C) (m : Frame) (hm : Marked m C)
    (one : ∀ k, m.gap k = 1) : C.card ≤ 112 :=
  RecordedFrame.bound1111 C hc m one (fun k => anchor_of_run atlas needed checked C hc m hm k (one k))

end SevenCycle.Adjacent.FrontSearch
