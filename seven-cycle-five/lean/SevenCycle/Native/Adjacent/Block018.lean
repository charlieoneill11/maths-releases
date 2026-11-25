import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [273, 289). -/
theorem adjacent_block018 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 273 289 = true := by
  native_decide

end SevenCycle.Native
