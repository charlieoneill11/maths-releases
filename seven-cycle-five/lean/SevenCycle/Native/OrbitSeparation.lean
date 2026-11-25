import SevenCycle.Atlas.Invariants

namespace SevenCycle.Native

/-- The invariant in `Atlas.Invariants.energiesDistinct_sound` has 1,016 different values. -/
theorem atlas_energies_checked : Atlas.Invariants.energiesDistinct atlasPlanes = true := by
  native_decide

end SevenCycle.Native
