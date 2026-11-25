import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [593, 609). -/
theorem adjacent_block038 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 593 609 = true := by
  native_decide

end SevenCycle.Native
