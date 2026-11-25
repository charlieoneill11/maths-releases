import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [641, 657). -/
theorem adjacent_block041 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 641 657 = true := by
  native_decide

end SevenCycle.Native
