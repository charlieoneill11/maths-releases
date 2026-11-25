import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [545, 561). -/
theorem adjacent_block035 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 545 561 = true := by
  native_decide

end SevenCycle.Native
