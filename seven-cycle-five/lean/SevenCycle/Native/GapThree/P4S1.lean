import SevenCycle.TypeThree.Shards

namespace SevenCycle.Native

/-- Complete domain, query-slot part 4, source representative index congruent to 1 modulo four. -/
theorem gap_three_p4_s1 : TypeThree.checkShard 4 1 atlasPlanes = true := by
  native_decide

end SevenCycle.Native
