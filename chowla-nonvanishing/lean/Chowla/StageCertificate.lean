import Chowla.StageOneChecked
import Chowla.Native.Stage2
import Chowla.Native.Stage3
import Chowla.Native.Stage4
import Chowla.Native.Stage5
import Chowla.Stage6Checked
import Chowla.Stage7Checked
import Chowla.Stage8Checked
import Chowla.Enclosure

namespace Chowla

open Checker

private theorem verifiedStage2 : reportedStage2.Sound 1 ∧ reportedStage2.check 1 = true :=
  stageCheck_sound 1 _ _ Native.stage2_checked (fun _ => verifiedStage1)

private theorem verifiedStage3 : reportedStage3.Sound 2 ∧ reportedStage3.check 2 = true :=
  stageCheck_sound 2 _ _ Native.stage3_checked (fun _ => verifiedStage2)

private theorem verifiedStage4 : reportedStage4.Sound 3 ∧ reportedStage4.check 3 = true :=
  stageCheck_sound 3 _ _ Native.stage4_checked (fun _ => verifiedStage3)

private theorem verifiedStage5 : reportedStage5.Sound 4 ∧ reportedStage5.check 4 = true :=
  stageCheck_sound 4 _ _ Native.stage5_checked (fun _ => verifiedStage4)

private theorem verifiedStage6 : reportedStage6.Sound 5 ∧ reportedStage6.check 5 = true :=
  stageCheck_sound 5 _ _ stage6Checked (fun _ => verifiedStage5)

private theorem verifiedStage7 : reportedStage7.Sound 6 ∧ reportedStage7.check 6 = true :=
  stageCheck_sound 6 _ _ stage7Checked (fun _ => verifiedStage6)

private theorem verifiedStage8 : reportedStage8.Sound 7 ∧ reportedStage8.check 7 = true :=
  stageCheck_sound 7 _ _ stage8Checked (fun _ => verifiedStage7)

/-- Each certificate stage supplies real enclosures and an exact strict comparison. -/
theorem certificate_stage (i : Fin 8) :
    ∃ b : StageBounds, b.Sound i ∧ b.check i = true := by
  fin_cases i
  · exact ⟨reportedStage1, verifiedStage1⟩
  · exact ⟨reportedStage2, verifiedStage2⟩
  · exact ⟨reportedStage3, verifiedStage3⟩
  · exact ⟨reportedStage4, verifiedStage4⟩
  · exact ⟨reportedStage5, verifiedStage5⟩
  · exact ⟨reportedStage6, verifiedStage6⟩
  · exact ⟨reportedStage7, verifiedStage7⟩
  · exact ⟨reportedStage8, verifiedStage8⟩

/-- Proposition 32 gives the explicit strict certificate on the paper's real model. -/
theorem certificate : CertificateStatement :=
  certificate_of_final_bounds reportedStage8 verifiedStage8.1 verifiedStage8.2 cot_upper

end Chowla
