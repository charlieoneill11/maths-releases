import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [561, 577). -/
theorem adjacent_block036 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 561 577 = true := by
  native_decide

end SevenCycle.Native
