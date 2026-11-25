import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [305, 321). -/
theorem adjacent_block020 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 305 321 = true := by
  native_decide

end SevenCycle.Native
