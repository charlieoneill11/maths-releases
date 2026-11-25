import SevenCycle.Atlas.Chain

namespace SevenCycle.Native

/-- The normalized 34-word search for planar orbit 2 and deficit pattern 2. -/
theorem exclude34_r2_d2 : Atlas.CubePlanes.exclude34Check #[(2,2)] = true := by
  native_decide

end SevenCycle.Native
