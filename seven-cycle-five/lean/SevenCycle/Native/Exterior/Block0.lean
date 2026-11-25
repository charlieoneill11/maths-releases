import SevenCycle.Adjacent.UnionTable

namespace SevenCycle.Native

/-- Check the exterior certificates for union rows 0 through 443. -/
theorem exterior_block0 :
    Adjacent.UnionTable.windowCheck Adjacent.UnionData.rows (0, 444) = true := by
  native_decide

end SevenCycle.Native
