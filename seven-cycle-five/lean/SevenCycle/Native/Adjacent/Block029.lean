import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [449, 465). -/
theorem adjacent_block029 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 449 465 = true := by
  native_decide

end SevenCycle.Native
