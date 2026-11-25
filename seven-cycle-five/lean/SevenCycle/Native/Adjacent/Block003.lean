import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [33, 49). -/
theorem adjacent_block003 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 33 49 = true := by
  native_decide

end SevenCycle.Native
