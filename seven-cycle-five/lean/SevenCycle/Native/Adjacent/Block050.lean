import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [785, 801). -/
theorem adjacent_block050 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 785 801 = true := by
  native_decide

end SevenCycle.Native
