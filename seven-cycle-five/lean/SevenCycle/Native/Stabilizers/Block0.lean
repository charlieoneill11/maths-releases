import SevenCycle.Atlas.Stabilizers

namespace SevenCycle.Native

/-- Verify the stabiliser orders of atlas rows 0 through 253. -/
theorem stabilizers_block0 :
    Atlas.Stabilizers.blockCheck ⟨atlasPlanes, 0, 254⟩ = true := by
  native_decide

end SevenCycle.Native
