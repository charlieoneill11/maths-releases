import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [849, 865). -/
theorem adjacent_block054 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 849 865 = true := by
  native_decide

end SevenCycle.Native
