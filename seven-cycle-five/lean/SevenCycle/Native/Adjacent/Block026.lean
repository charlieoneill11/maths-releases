import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [401, 417). -/
theorem adjacent_block026 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 401 417 = true := by
  native_decide

end SevenCycle.Native
