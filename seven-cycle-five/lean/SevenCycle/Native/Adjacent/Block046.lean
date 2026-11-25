import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [721, 737). -/
theorem adjacent_block046 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 721 737 = true := by
  native_decide

end SevenCycle.Native
