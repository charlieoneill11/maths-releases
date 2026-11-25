import SevenCycle.Atlas.Chain

namespace SevenCycle.Native

/-- The normalized 34-word search for planar orbit 2 and deficit pattern 0. -/
theorem exclude34_r2_d0 : Atlas.CubePlanes.exclude34Check #[(2,0)] = true := by
  native_decide

end SevenCycle.Native
