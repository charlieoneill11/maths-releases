import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [529, 545). -/
theorem adjacent_block034 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 529 545 = true := by
  native_decide

end SevenCycle.Native
