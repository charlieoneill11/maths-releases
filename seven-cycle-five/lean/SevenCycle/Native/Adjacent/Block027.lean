import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [417, 433). -/
theorem adjacent_block027 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 417 433 = true := by
  native_decide

end SevenCycle.Native
