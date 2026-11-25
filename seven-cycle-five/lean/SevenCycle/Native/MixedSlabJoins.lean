import SevenCycle.Adjacent.MixedSlabs
import SevenCycle.Adjacent.MixedSlabData
import SevenCycle.Adjacent.Stage6.Data

namespace SevenCycle.Native
open Adjacent

/-- All compatible 1112 triples are excluded by the three physical slabs. -/
theorem mixed1112_slab_join :
    MixedSlabs.check #v[1,1,1,2] MixedSlabData.rows1112 (fun _ => false) = true := by
  native_decide

/-- Every compatible physical pair for 1122 belongs to the four-row final table. -/
theorem mixed1122_slab_join :
    MixedSlabs.check #v[1,1,2,2] MixedSlabData.rows1122 (fun b => (Stage6.maskTable false).contains ⟨b⟩) = true := by
  native_decide

/-- Every compatible physical pair for 1123 belongs to the 64-row final table. -/
theorem mixed1123_slab_join :
    MixedSlabs.check #v[1,1,2,3] MixedSlabData.rows1123 (fun b => (Stage6.maskTable true).contains ⟨b⟩) = true := by
  native_decide

end SevenCycle.Native
