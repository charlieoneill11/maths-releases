import SevenCycle.Atlas.Complete33

namespace SevenCycle.Native

/-- Certify every normalized 33-code for planar orbit 1 and deficit chunk 0. -/
theorem classify33_r1_g0 : Atlas.classify33Check (Atlas.jobs33 1 0) = true := by
  native_decide

end SevenCycle.Native
