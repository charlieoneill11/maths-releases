import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [881, 897). -/
theorem adjacent_block056 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 881 897 = true := by
  native_decide

end SevenCycle.Native
