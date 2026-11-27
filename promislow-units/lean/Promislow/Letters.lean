import Promislow.Atoms

namespace Promislow
noncomputable section
open Sparse

-- Reduce the two halves independently; these identities are considerably smaller
-- than multiplying two eight-atom numerator expansions.
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

theorem halfNorm (l : Letter) :
    val (firstHalf l) * val (prefixAdj l) = F l ^ 4 ∧
    val (prefixAdj l) * val (firstHalf l) = F l ^ 4 ∧
    val (lastHalf l) * val (suffixAdj l) = F l ^ 4 ∧
    val (suffixAdj l) * val (lastHalf l) = F l ^ 4 := by
  unfold F
  simp only [← val_mul, ← val_pow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply congrArg val <;> cases l <;> native_decide

theorem splitNum (l : Letter) :
    N l false = val (firstHalf l) * val (lastHalf l) ∧
    N l true = val (suffixAdj l) * val (prefixAdj l) := by
  unfold N
  simp only [← val_mul]
  cases l <;> constructor <;> apply congrArg val <;> native_decide

end
end Promislow
