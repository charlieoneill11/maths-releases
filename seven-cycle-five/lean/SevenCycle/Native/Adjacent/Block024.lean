import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [369, 385). -/
theorem adjacent_block024 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 369 385 = true := by
  native_decide

end SevenCycle.Native
