import SevenCycle.TypeThree.Shards

namespace SevenCycle.Native

/-- Complete domain, query-slot part 3, source representative index congruent to 1 modulo four. -/
theorem gap_three_p3_s1 : TypeThree.checkShard 3 1 atlasPlanes = true := by
  native_decide

end SevenCycle.Native
