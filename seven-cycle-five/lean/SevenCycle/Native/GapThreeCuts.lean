import SevenCycle.AtlasData
import SevenCycle.TypeThree.DistinctCuts

namespace SevenCycle.Native

/-- A planar disagreement for each representative, each axis and each gap-three pair.
The interpretation of the Boolean is `TypeThree.cutsDistinct_sound`. -/
theorem atlas_gap_three_cuts : TypeThree.cutsDistinct atlasPlanes = true := by
  native_decide

end SevenCycle.Native
