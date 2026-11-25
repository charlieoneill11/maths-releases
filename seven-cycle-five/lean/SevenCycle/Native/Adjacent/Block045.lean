import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [705, 721). -/
theorem adjacent_block045 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 705 721 = true := by
  native_decide

end SevenCycle.Native
