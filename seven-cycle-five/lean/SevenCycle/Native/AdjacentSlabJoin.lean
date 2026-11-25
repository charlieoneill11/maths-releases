import SevenCycle.Adjacent.Frames
import SevenCycle.Adjacent.SlabData
import SevenCycle.Adjacent.UnionMasks

namespace SevenCycle.Native

open Adjacent Adjacent.SlabJoin

/-- Over all four framed domains generated from the candidate 1111 slabs,
the union of every unpruned compatible quartet is listed in the exterior table. -/
theorem adjacent1111_slab_join :
    checkSlabs (frameDomains SlabData.rows) neighborTable UnionMasks.knownUnionMasks.contains = true := by
  native_decide

end SevenCycle.Native
