import SevenCycle.Atlas.Complete33

namespace SevenCycle.Native

/-- Certify every normalized 33-code for planar orbit 2 and deficit chunk 7. -/
theorem classify33_r2_g7 : Atlas.classify33Check (Atlas.jobs33 2 7) = true := by
  native_decide

end SevenCycle.Native
