import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [257, 273). -/
theorem adjacent_block017 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 257 273 = true := by
  native_decide

end SevenCycle.Native
