import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [177, 193). -/
theorem adjacent_block012 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 177 193 = true := by
  native_decide

end SevenCycle.Native
