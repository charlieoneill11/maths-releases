import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [689, 705). -/
theorem adjacent_block044 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 689 705 = true := by
  native_decide

end SevenCycle.Native
