import SevenCycle.Native.MixedBands1122
import SevenCycle.Native.MixedBands1123

namespace SevenCycle.Adjacent.Stage6

open Blueprint.SearchSpec

/-- Neither an 1122 nor an 1123 physical union in the marked frame
extends to all the required remaining projections. -/
theorem noRemaining (p : Bool) (i : Fin (rowCount p)) {D : Points}
    (hD : SlabJoin.Stores (rowMask p i) D) (W : Family) : ¬ Remaining (frame p) D W := by
  apply rowsCheck_sound p _ i hD W
  cases p
  · exact Native.mixedBands1122
  · exact Native.mixedBands1123

end SevenCycle.Adjacent.Stage6
