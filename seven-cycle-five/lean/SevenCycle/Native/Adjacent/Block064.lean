import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [1009, 1016). -/
theorem adjacent_block064 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 1009 1016 = true := by
  native_decide

end SevenCycle.Native
