import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [193, 209). -/
theorem adjacent_block013 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 193 209 = true := by
  native_decide

end SevenCycle.Native
