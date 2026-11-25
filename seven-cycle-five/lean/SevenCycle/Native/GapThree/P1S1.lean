import SevenCycle.TypeThree.Shards

namespace SevenCycle.Native

/-- Complete domain, query-slot part 1, source representative index congruent to 1 modulo four. -/
theorem gap_three_p1_s1 : TypeThree.checkShard 1 1 atlasPlanes = true := by
  native_decide

end SevenCycle.Native
