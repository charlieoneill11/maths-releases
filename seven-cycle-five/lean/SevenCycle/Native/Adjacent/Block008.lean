import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [113, 129). -/
theorem adjacent_block008 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 113 129 = true := by
  native_decide

end SevenCycle.Native
