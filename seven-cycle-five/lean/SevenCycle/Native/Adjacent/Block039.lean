import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [609, 625). -/
theorem adjacent_block039 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 609 625 = true := by
  native_decide

end SevenCycle.Native
