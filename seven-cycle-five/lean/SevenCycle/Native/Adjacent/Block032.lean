import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [497, 513). -/
theorem adjacent_block032 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 497 513 = true := by
  native_decide

end SevenCycle.Native
