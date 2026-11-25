import SevenCycle.TypeThree.Shards

namespace SevenCycle.Native

/-- Complete domain, query-slot part 1, source representative index congruent to 3 modulo four. -/
theorem gap_three_p1_s3 : TypeThree.checkShard 1 3 atlasPlanes = true := by
  native_decide

end SevenCycle.Native
