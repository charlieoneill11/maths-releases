import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [961, 977). -/
theorem adjacent_block061 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 961 977 = true := by
  native_decide

end SevenCycle.Native
