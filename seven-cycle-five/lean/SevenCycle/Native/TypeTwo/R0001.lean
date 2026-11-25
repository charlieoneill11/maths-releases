import SevenCycle.TypeTwo.Coverage

namespace SevenCycle.Native

/-- All first support representatives and all labelled opposite supports from class one. -/
theorem typeTwo_0001 : TypeTwo.Search.check atlasPlanes atlasPlanes (atlasPlanes.extract 1 2) = true := by
  native_decide

end SevenCycle.Native
