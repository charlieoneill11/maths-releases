import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [465, 481). -/
theorem adjacent_block030 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 465 481 = true := by
  native_decide

end SevenCycle.Native
