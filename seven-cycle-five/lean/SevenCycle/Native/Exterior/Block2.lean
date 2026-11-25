import SevenCycle.Adjacent.UnionTable

namespace SevenCycle.Native

/-- Check the exterior certificates for union rows 888 through 1331. -/
theorem exterior_block2 :
    Adjacent.UnionTable.windowCheck Adjacent.UnionData.rows (888, 1332) = true := by
  native_decide

end SevenCycle.Native
