import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [833, 849). -/
theorem adjacent_block053 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 833 849 = true := by
  native_decide

end SevenCycle.Native
