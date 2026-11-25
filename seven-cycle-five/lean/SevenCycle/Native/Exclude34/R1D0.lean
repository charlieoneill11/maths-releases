import SevenCycle.Atlas.Chain

namespace SevenCycle.Native

/-- The normalized 34-word search for planar orbit 1 and deficit pattern 0. -/
theorem exclude34_r1_d0 : Atlas.CubePlanes.exclude34Check #[(1,0)] = true := by
  native_decide

end SevenCycle.Native
