import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [17, 33). -/
theorem adjacent_block002 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 17 33 = true := by
  native_decide

end SevenCycle.Native
