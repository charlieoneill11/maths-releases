import SevenCycle.Atlas.Stabilizers

namespace SevenCycle.Native

/-- Verify the stabiliser orders of atlas rows 762 through 1015. -/
theorem stabilizers_block3 :
    Atlas.Stabilizers.blockCheck ⟨atlasPlanes, 762, 254⟩ = true := by
  native_decide

end SevenCycle.Native
