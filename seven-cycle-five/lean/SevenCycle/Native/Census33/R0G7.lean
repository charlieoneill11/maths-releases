import SevenCycle.Atlas.Complete33

namespace SevenCycle.Native

/-- Certify every normalized 33-code for planar orbit 0 and deficit chunk 7. -/
theorem classify33_r0_g7 : Atlas.classify33Check (Atlas.jobs33 0 7) = true := by
  native_decide

end SevenCycle.Native
