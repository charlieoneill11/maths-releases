import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [81, 97). -/
theorem adjacent_block006 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 81 97 = true := by
  native_decide

end SevenCycle.Native
