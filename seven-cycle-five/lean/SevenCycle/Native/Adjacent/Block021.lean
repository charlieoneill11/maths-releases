import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [321, 337). -/
theorem adjacent_block021 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 321 337 = true := by
  native_decide

end SevenCycle.Native
