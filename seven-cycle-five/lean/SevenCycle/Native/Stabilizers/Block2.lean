import SevenCycle.Atlas.Stabilizers

namespace SevenCycle.Native

/-- Verify the stabiliser orders of atlas rows 508 through 761. -/
theorem stabilizers_block2 :
    Atlas.Stabilizers.blockCheck ⟨atlasPlanes, 508, 254⟩ = true := by
  native_decide

end SevenCycle.Native
