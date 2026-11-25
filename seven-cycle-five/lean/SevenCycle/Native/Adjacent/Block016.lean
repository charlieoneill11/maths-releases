import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [241, 257). -/
theorem adjacent_block016 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 241 257 = true := by
  native_decide

end SevenCycle.Native
