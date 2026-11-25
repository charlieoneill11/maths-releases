import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [97, 113). -/
theorem adjacent_block007 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 97 113 = true := by
  native_decide

end SevenCycle.Native
