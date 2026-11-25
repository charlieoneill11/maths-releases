import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [929, 945). -/
theorem adjacent_block059 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 929 945 = true := by
  native_decide

end SevenCycle.Native
