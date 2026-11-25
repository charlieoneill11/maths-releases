import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Adjacent.PrefixHint

namespace SevenCycle.Native

/-- All 1,016 anchors and every labelled image of target class zero, with all
ordered adjacent profiles checked through the six-band source table. -/
theorem adjacent_block000 :
    Adjacent.FrontSearch.range Adjacent.PrefixHint.needed 0 1 = true := by
  native_decide

end SevenCycle.Native
