import SevenCycleRuntime.AdjacentDomains
import SevenCycleRuntime.PrefixHint

namespace SevenCycle.Adjacent.PrefixHint

/-- Restrict the Stage 4 domain index to likely marked prefixes. Missing
keys still reach the terminal checker through the band's fallback branch. -/
@[inline] def needed (k : BandJoin.Prefix) : Bool :=
  containsTriple k.first k.second k.middle

end SevenCycle.Adjacent.PrefixHint
