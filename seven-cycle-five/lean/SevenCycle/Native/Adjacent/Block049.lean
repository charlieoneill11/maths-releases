import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [769, 785). -/
theorem adjacent_block049 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 769 785 = true := by
  native_decide

end SevenCycle.Native
