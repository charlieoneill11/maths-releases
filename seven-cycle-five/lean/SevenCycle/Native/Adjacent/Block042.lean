import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [657, 673). -/
theorem adjacent_block042 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 657 673 = true := by
  native_decide

end SevenCycle.Native
