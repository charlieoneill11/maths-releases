import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [977, 993). -/
theorem adjacent_block062 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 977 993 = true := by
  native_decide

end SevenCycle.Native
