import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [897, 913). -/
theorem adjacent_block057 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 897 913 = true := by
  native_decide

end SevenCycle.Native
