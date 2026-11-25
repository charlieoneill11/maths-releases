import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [993, 1009). -/
theorem adjacent_block063 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 993 1009 = true := by
  native_decide

end SevenCycle.Native
