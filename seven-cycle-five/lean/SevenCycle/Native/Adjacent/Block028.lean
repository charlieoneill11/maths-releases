import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [433, 449). -/
theorem adjacent_block028 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 433 449 = true := by
  native_decide

end SevenCycle.Native
