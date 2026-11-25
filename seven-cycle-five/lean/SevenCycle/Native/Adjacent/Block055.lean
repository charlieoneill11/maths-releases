import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- Check every ordered adjacent profile and all anchors against target
classes in the half-open interval [865, 881). -/
theorem adjacent_block055 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 865 881 = true := by
  native_decide

end SevenCycle.Native
