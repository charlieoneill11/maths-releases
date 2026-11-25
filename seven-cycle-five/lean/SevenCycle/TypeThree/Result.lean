import SevenCycle.Atlas.Census33
import SevenCycle.Native.GapThree.P0S0
import SevenCycle.Native.GapThree.P0S1
import SevenCycle.Native.GapThree.P0S2
import SevenCycle.Native.GapThree.P0S3
import SevenCycle.Native.GapThree.P1S0
import SevenCycle.Native.GapThree.P1S1
import SevenCycle.Native.GapThree.P1S2
import SevenCycle.Native.GapThree.P1S3
import SevenCycle.Native.GapThree.P2S0
import SevenCycle.Native.GapThree.P2S1
import SevenCycle.Native.GapThree.P2S2
import SevenCycle.Native.GapThree.P2S3
import SevenCycle.Native.GapThree.P3S0
import SevenCycle.Native.GapThree.P3S1
import SevenCycle.Native.GapThree.P3S2
import SevenCycle.Native.GapThree.P3S3
import SevenCycle.Native.GapThree.P4S0
import SevenCycle.Native.GapThree.P4S1
import SevenCycle.Native.GapThree.P4S2
import SevenCycle.Native.GapThree.P4S3

/-! # The complete type-three exclusion

The twenty native equalities establish the normalized join exclusion of Lemma
18. The normalization and atlas coverage then give Proposition 17. -/

namespace SevenCycle.TypeThree
open Blueprint Proof

theorem shards_checked (p : Fin 5) (strip : Fin 4) : checkShard p strip atlasPlanes = true := by
  fin_cases p <;> fin_cases strip
  · exact Native.gap_three_p0_s0
  · exact Native.gap_three_p0_s1
  · exact Native.gap_three_p0_s2
  · exact Native.gap_three_p0_s3
  · exact Native.gap_three_p1_s0
  · exact Native.gap_three_p1_s1
  · exact Native.gap_three_p1_s2
  · exact Native.gap_three_p1_s3
  · exact Native.gap_three_p2_s0
  · exact Native.gap_three_p2_s1
  · exact Native.gap_three_p2_s2
  · exact Native.gap_three_p2_s3
  · exact Native.gap_three_p3_s0
  · exact Native.gap_three_p3_s1
  · exact Native.gap_three_p3_s2
  · exact Native.gap_three_p3_s3
  · exact Native.gap_three_p4_s0
  · exact Native.gap_three_p4_s1
  · exact Native.gap_three_p4_s2
  · exact Native.gap_three_p4_s3

/-- Lemma 18 on the complete normalized anchor and transverse tables. -/
theorem no_join : NoJoined (packRows atlasPlanes Bitsets.translationImages)
    (packRows atlasPlanes Bitsets.orbitImages) :=
  noJoined_of_shards shards_checked

/-- Proposition 17 excludes the type-three full-band pattern for every code. -/
theorem exclude (C : Finset (Tuple 4)) (hc : packing cycleStep C) :
    ¬ ∀ k, ∃ t ∈ fullStarts C k, t + 3 ∈ fullStarts C k :=
  exclude_of_shards Atlas.atlas_complete shards_checked C hc

end SevenCycle.TypeThree
