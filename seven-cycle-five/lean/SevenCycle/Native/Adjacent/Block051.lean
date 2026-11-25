import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [801, 817). -/
theorem adjacent_block051 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 801 817 = true := by
  native_decide

end SevenCycle.Native
