import SevenCycle.Adjacent.FrontRetention
import SevenCycle.Adjacent.MixedRecorded

namespace SevenCycle.Adjacent.FrontSearch
open Proof Blueprint SearchSpec

/-- Proposition 12 for a genuine marked code, after checking all target-class
intervals. This applies to every adjacent distance profile. -/
theorem adjacent_bound (atlas : Contacts.AtlasComplete) (needed : BandJoin.Prefix → Bool)
    (checked : ScanFused.checkClasses atlasPlanes (gate needed) SlabTables.leaf = true)
    {C : Points} (hc : packing cycleStep C) {m : Frame} (hm : Marked m C)
    (adjacent : ∃ k, m.gap k = 1) : C.card ≤ 112 := by
  by_cases all : ∀ j, m.gap j = 1
  · exact bound1111_of_run atlas needed checked C hc m hm all
  · exact (MixedCommon.reject hc hm adjacent (Classical.not_forall.mp all)
      (fun k hk => anchor_of_run atlas needed checked C hc m hm k hk)).elim

end SevenCycle.Adjacent.FrontSearch
