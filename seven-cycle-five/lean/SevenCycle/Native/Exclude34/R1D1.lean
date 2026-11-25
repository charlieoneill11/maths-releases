import SevenCycle.Atlas.Chain

namespace SevenCycle.Native

/-- The normalized 34-word search for planar orbit 1 and deficit pattern 1. -/
theorem exclude34_r1_d1 : Atlas.CubePlanes.exclude34Check #[(1,1)] = true := by
  native_decide

end SevenCycle.Native
