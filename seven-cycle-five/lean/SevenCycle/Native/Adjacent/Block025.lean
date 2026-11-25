import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [385, 401). -/
theorem adjacent_block025 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 385 401 = true := by
  native_decide

end SevenCycle.Native
