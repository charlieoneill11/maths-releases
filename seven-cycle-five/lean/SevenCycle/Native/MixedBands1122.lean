import SevenCycle.Adjacent.Stage6.Bands

namespace SevenCycle.Native

/-- Rule out a full remaining band for each physical union of profile 1122. -/
theorem mixedBands1122 : Adjacent.Stage6.rowsCheck false = true := by
  native_decide

end SevenCycle.Native
