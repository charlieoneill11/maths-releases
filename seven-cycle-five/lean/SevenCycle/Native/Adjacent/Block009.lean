import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [129, 145). -/
theorem adjacent_block009 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 129 145 = true := by
  native_decide

end SevenCycle.Native
