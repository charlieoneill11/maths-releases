import SevenCycle.TypeTwo.Fast

namespace SevenCycle.Native

/-- Opposite support classes 512 through 527, all source classes and eight gap assignments. -/
theorem typeTwo_chunk_32 : TypeTwo.Search.chunk 32 = true := by
  native_decide

end SevenCycle.Native
