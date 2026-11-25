import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [65, 81). -/
theorem adjacent_block005 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 65 81 = true := by
  native_decide

end SevenCycle.Native
