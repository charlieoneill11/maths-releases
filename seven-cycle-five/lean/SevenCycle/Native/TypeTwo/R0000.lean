import SevenCycle.TypeTwo.Coverage

namespace SevenCycle.Native

/-- All first support representatives and all labelled opposite supports from class zero. -/
theorem typeTwo_0000 : TypeTwo.Search.check atlasPlanes atlasPlanes (atlasPlanes.extract 0 1) = true := by
  native_decide

end SevenCycle.Native
