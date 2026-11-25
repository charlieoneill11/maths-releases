import HadwigerNelson.Wave.Geometry.Partial

namespace HadwigerNelson.Centres
open Set

def partialProfile (W : Wave.Datum) : Prop :=
  W.x = 923111560246/10^12 ∧ W.y0 = 918/100000 ∧
    ∀ i : Fin 17, ∀ u ∈ Icc (0:ℝ) 1,
      W.left (((i:ℝ)+u)*54/100000) =
        ((1-u)*(PartialWave.leftKnots[i.val]!.2 : ℝ) + u*(PartialWave.leftKnots[i.val+1]!.2 : ℝ))/10^12

end HadwigerNelson.Centres
