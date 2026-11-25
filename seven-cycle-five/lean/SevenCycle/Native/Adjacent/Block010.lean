import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [145, 161). -/
theorem adjacent_block010 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 145 161 = true := by
  native_decide

end SevenCycle.Native
