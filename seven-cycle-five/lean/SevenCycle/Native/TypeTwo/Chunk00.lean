import SevenCycle.Native.TypeTwo.R0000
import SevenCycle.Native.TypeTwo.R0001
import SevenCycle.TypeTwo.Fast

namespace SevenCycle.Native

/-- Opposite support classes 0 through 15, all source classes and eight gap assignments. -/
theorem typeTwo_0002_to_0016 : TypeTwo.Search.fastCheck atlasPlanes atlasPlanes (atlasPlanes.extract 2 16) = true := by
  native_decide

theorem typeTwo_chunk_00 : TypeTwo.Search.chunk 0 = true := by
  simpa only [TypeTwo.Search.chunk, if_pos rfl, typeTwo_0000, typeTwo_0001, Bool.true_and] using typeTwo_0002_to_0016

end SevenCycle.Native
