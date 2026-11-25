import SevenCycle.Adjacent.UnionTable

namespace SevenCycle.Native

/-- Check the exterior certificates for union rows 1332 through 1775. -/
theorem exterior_block3 :
    Adjacent.UnionTable.windowCheck Adjacent.UnionData.rows (1332, 1776) = true := by
  native_decide

end SevenCycle.Native
