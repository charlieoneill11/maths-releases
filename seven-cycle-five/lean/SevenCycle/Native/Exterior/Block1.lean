import SevenCycle.Adjacent.UnionTable

namespace SevenCycle.Native

/-- Check the exterior certificates for union rows 444 through 887. -/
theorem exterior_block1 :
    Adjacent.UnionTable.windowCheck Adjacent.UnionData.rows (444, 888) = true := by
  native_decide

end SevenCycle.Native
