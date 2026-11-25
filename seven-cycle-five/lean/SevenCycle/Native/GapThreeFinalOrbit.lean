import SevenCycle.TypeThree.FastCuts
import SevenCycle.TypeThree.Check

namespace SevenCycle.Native
open TypeThree

set_option maxRecDepth 8192 in
/-- The final class subproblem of the minimum-class decomposition: the anchor
uses its 343 translations, and each of the other seven supports ranges over
all 16,464 descriptions of a moved representative. -/
def gapThreeFinalOrbit : Block :=
  let row := atlasPlanes[1015]'(by decide +kernel)
  ⟨#[row], #[row], 0, 1⟩

theorem gap_three_final_orbit : checkBlock fastCutsOf gapThreeFinalOrbit = true := by
  native_decide

end SevenCycle.Native
