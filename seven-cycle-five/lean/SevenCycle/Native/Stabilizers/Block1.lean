import SevenCycle.Atlas.Stabilizers

namespace SevenCycle.Native

/-- Verify the stabiliser orders of atlas rows 254 through 507. -/
theorem stabilizers_block1 :
    Atlas.Stabilizers.blockCheck ⟨atlasPlanes, 254, 254⟩ = true := by
  native_decide

end SevenCycle.Native
