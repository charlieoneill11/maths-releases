import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [513, 529). -/
theorem adjacent_block033 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 513 529 = true := by
  native_decide

end SevenCycle.Native
