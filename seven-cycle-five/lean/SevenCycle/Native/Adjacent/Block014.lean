import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [209, 225). -/
theorem adjacent_block014 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 209 225 = true := by
  native_decide

end SevenCycle.Native
