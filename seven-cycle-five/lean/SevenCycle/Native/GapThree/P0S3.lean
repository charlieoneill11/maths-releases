import SevenCycle.TypeThree.Shards

namespace SevenCycle.Native

/-- Complete domain, query-slot part 0, source representative index congruent to 3 modulo four. -/
theorem gap_three_p0_s3 : TypeThree.checkShard 0 3 atlasPlanes = true := by
  native_decide

end SevenCycle.Native
