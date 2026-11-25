import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [913, 929). -/
theorem adjacent_block058 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 913 929 = true := by
  native_decide

end SevenCycle.Native
