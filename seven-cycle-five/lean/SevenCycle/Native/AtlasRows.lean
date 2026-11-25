import SevenCycle.Atlas.Rows

namespace SevenCycle.Native

/-- All 1,016 input rows pass the cardinality and pairwise separation checker.
The interpretation of this equality is proved by `Atlas.rowsValid_sound`. -/
theorem atlas_rows_checked : Atlas.rowsValid atlasPlanes = true := by
  native_decide

end SevenCycle.Native
