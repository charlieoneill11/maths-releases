import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [289, 305). -/
theorem adjacent_block019 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 289 305 = true := by
  native_decide

end SevenCycle.Native
