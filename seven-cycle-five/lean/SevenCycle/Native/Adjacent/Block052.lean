import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [817, 833). -/
theorem adjacent_block052 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 817 833 = true := by
  native_decide

end SevenCycle.Native
