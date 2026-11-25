import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [737, 753). -/
theorem adjacent_block047 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 737 753 = true := by
  native_decide

end SevenCycle.Native
