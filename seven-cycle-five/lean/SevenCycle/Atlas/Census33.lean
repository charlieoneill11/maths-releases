import SevenCycle.Native.Census33.R0G0
import SevenCycle.Native.Census33.R0G1
import SevenCycle.Native.Census33.R0G2
import SevenCycle.Native.Census33.R0G3
import SevenCycle.Native.Census33.R0G4
import SevenCycle.Native.Census33.R0G5
import SevenCycle.Native.Census33.R0G6
import SevenCycle.Native.Census33.R0G7
import SevenCycle.Native.Census33.R1G0
import SevenCycle.Native.Census33.R1G1
import SevenCycle.Native.Census33.R1G2
import SevenCycle.Native.Census33.R1G3
import SevenCycle.Native.Census33.R1G4
import SevenCycle.Native.Census33.R1G5
import SevenCycle.Native.Census33.R1G6
import SevenCycle.Native.Census33.R1G7
import SevenCycle.Native.Census33.R2G0
import SevenCycle.Native.Census33.R2G1
import SevenCycle.Native.Census33.R2G2
import SevenCycle.Native.Census33.R2G3
import SevenCycle.Native.Census33.R2G4
import SevenCycle.Native.Census33.R2G5
import SevenCycle.Native.Census33.R2G6
import SevenCycle.Native.Census33.R2G7
import SevenCycle.Atlas.PlanarKernel

namespace SevenCycle.Atlas

open Blueprint Proof

/-- Every labelled 33-code in the cube is an image of an actual released atlas row. -/
theorem atlas_complete (C : Finset (Tuple 3)) (hc : packing cycleStep C) (hs : C.card = 33) :
    ∃ r : Fin atlasPlanes.size, ∃ g : Isometry 3, C = actOnCode g (atlasRepresentative r) := by
  have checks (r : Fin 3) (g : Fin 8) : classify33Check (jobs33 r g) = true := by
    fin_cases r <;> fin_cases g
    · exact Native.classify33_r0_g0
    · exact Native.classify33_r0_g1
    · exact Native.classify33_r0_g2
    · exact Native.classify33_r0_g3
    · exact Native.classify33_r0_g4
    · exact Native.classify33_r0_g5
    · exact Native.classify33_r0_g6
    · exact Native.classify33_r0_g7
    · exact Native.classify33_r1_g0
    · exact Native.classify33_r1_g1
    · exact Native.classify33_r1_g2
    · exact Native.classify33_r1_g3
    · exact Native.classify33_r1_g4
    · exact Native.classify33_r1_g5
    · exact Native.classify33_r1_g6
    · exact Native.classify33_r1_g7
    · exact Native.classify33_r2_g0
    · exact Native.classify33_r2_g1
    · exact Native.classify33_r2_g2
    · exact Native.classify33_r2_g3
    · exact Native.classify33_r2_g4
    · exact Native.classify33_r2_g5
    · exact Native.classify33_r2_g6
    · exact Native.classify33_r2_g7
  apply atlas_complete_of_jobs Planar.Kernel.planar_classification _ C hc hs
  intro r p
  obtain ⟨g,hg⟩ := jobs33_cover r p
  exact ⟨jobs33 r g, hg, checks r g⟩

end SevenCycle.Atlas
