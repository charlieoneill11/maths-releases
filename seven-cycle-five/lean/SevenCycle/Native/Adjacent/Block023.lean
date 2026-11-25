import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [353, 369). -/
theorem adjacent_block023 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 353 369 = true := by
  native_decide

end SevenCycle.Native
