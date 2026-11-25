import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [481, 497). -/
theorem adjacent_block031 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 481 497 = true := by
  native_decide

end SevenCycle.Native
