import SevenCycle.Native.Exclude34.R0D0
import SevenCycle.Native.Exclude34.R0D1
import SevenCycle.Native.Exclude34.R0D2
import SevenCycle.Native.Exclude34.R0D3
import SevenCycle.Native.Exclude34.R1D0
import SevenCycle.Native.Exclude34.R1D1
import SevenCycle.Native.Exclude34.R1D2
import SevenCycle.Native.Exclude34.R1D3
import SevenCycle.Native.Exclude34.R2D0
import SevenCycle.Native.Exclude34.R2D1
import SevenCycle.Native.Exclude34.R2D2
import SevenCycle.Native.Exclude34.R2D3
import SevenCycle.Atlas.Reduce34
import SevenCycle.Atlas.PlanarKernel

namespace SevenCycle.Atlas

open Blueprint Proof CubePlanes

/-- Every three-dimensional code has at most 33 words. -/
theorem card_le_thirty_three (C : Finset (Tuple 3)) (hc : packing cycleStep C) : C.card ≤ 33 := by
  have checks (r : Fin 3) (d : Fin 4) : exclude34Check #[(r,d)] = true := by
    fin_cases r <;> fin_cases d
    · exact Native.exclude34_r0_d0
    · exact Native.exclude34_r0_d1
    · exact Native.exclude34_r0_d2
    · exact Native.exclude34_r0_d3
    · exact Native.exclude34_r1_d0
    · exact Native.exclude34_r1_d1
    · exact Native.exclude34_r1_d2
    · exact Native.exclude34_r1_d3
    · exact Native.exclude34_r2_d0
    · exact Native.exclude34_r2_d1
    · exact Native.exclude34_r2_d2
    · exact Native.exclude34_r2_d3
  have planar := Planar.Kernel.planar_classification
  apply card_le_thirty_three_of_normalized (Planar.classificationCheck_sound _ planar) _ C hc
  intro D hD hs r hn d hd
  exact exclude34Check_sound planar #[(r,d)] (checks r d) D hD hs r hn d hd (by simp)

end SevenCycle.Atlas
