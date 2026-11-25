import HadwigerNelson.Certificate.Hole.PackSound
import HadwigerNelson.Certificate.Hole.TableSound

namespace HadwigerNelson.Certificate.Hole
open Forest
noncomputable section

/-- The rational sweep bounds the four collision parameters for every datum
with the fixed left wall; the right wall does not enter this computation. -/
theorem checkPacking_sound (W : Wave.Datum) (p : Centres.partialProfile W)
    (ok : checkPacking = true) :
    packingSum physical (fun _ => True) ≤ 150296106235/(10:ℝ)^18 ∧
    packingSum physical (fun t => d<t) ≤ 97911102803/(10:ℝ)^18 ∧
    2*packingSum physical (fun t => t≤d) ≤ 104770006866/(10:ℝ)^18 ∧
    2*packingSum physical (fun _ => True) ≤ 300592212470/(10:ℝ)^18 := by
  have upper (b : Band) := pack_upper_of_rows W p b (unitRows 16384) (fun i =>
    unitRow_value physical_agrees 16384 (i.val+1) (by omega))
  unfold checkPacking at ok
  dsimp only at ok
  obtain ⟨l,t,u,j⟩ := of_decide_eq_true ok
  refine ⟨(upper .all).trans ?_,(upper .above).trans ?_,?_,?_⟩
  · simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 l
  · simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 t
  · apply (mul_le_mul_of_nonneg_left (upper .below) (by norm_num : (0:ℝ)≤2)).trans
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 u
  · apply (mul_le_mul_of_nonneg_left (upper .all) (by norm_num : (0:ℝ)≤2)).trans
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 j

end
end HadwigerNelson.Certificate.Hole
