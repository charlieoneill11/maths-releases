import HadwigerNelson.Centres.ArcLabels

namespace HadwigerNelson.Centres
noncomputable section

def threshold (i : Fin 7) : ℝ := (tenths i:ℝ)*δ/10

def longSingles (X : Finset Plane) (i : Fin 7) : Finset (Arc X) := by
  classical exact Finset.univ.filter fun e ↦ ¬paired e ∧ threshold i ≤ dist (start e) (finish e)

end
end HadwigerNelson.Centres
