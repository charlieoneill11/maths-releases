import SevenCycle.Atlas.Chain

namespace SevenCycle.Native

/-- The normalized 34-word search for planar orbit 1 and deficit pattern 3. -/
theorem exclude34_r1_d3 : Atlas.CubePlanes.exclude34Check #[(1,3)] = true := by
  native_decide

end SevenCycle.Native
