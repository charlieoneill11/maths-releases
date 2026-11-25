import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [161, 177). -/
theorem adjacent_block011 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 161 177 = true := by
  native_decide

end SevenCycle.Native
