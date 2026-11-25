import HadwigerNelson.Certificate.Hole.Physical
import HadwigerNelson.Certificate.Hole.Pack
import HadwigerNelson.Packing.RationalCap
import HadwigerNelson.Forest.BlankPairs
import Mathlib.Analysis.Real.Pi.Bounds

namespace HadwigerNelson.Certificate.Hole
open Forest
noncomputable section
attribute [local instance] Classical.propDecidable

def Band.condition (b : Band) (t : ℝ) : Prop :=
  match b with
  | .all => True
  | .above => d < t
  | .below => t ≤ d

private theorem t_cast (i : ℕ) : (unitT i:ℝ) = unitBin i := by norm_num [unitT,unitWidth,unitBin,Centres.w]; ring

private theorem used_iff (b : Band) (i : ℕ) : b.used (unitT i) = true ↔ b.condition (unitBin i) := by
  have heq : (radiusD:ℝ) = d := by norm_num [radiusD,d,Centres.δ]
  cases b <;> simp only [Band.used,Band.condition,decide_eq_true_eq]
  · rw [← t_cast,← heq]; exact_mod_cast Iff.rfl
  · rw [← t_cast,← heq]; exact_mod_cast Iff.rfl

private theorem denom_pos : (0:ℝ) < denom := by norm_num [denom,PartialWave.scale,PartialWave.xInt]

/-- Pointwise packing bounds all weighted terms, including the two restrictions
of the bin range used for T and U. -/
theorem pack_upper_of_rows (W : Wave.Datum) (p : Centres.partialProfile W) (b : Band)
    (rows : Array ℤ) (exactRows : ∀ i : Fin 16384,
    (rows[i.val+1]?.getD 0 : ℝ)/denom = unitStep physical (i.val+1)) :
    packingSum physical b.condition ≤ (packingUpper rows b:ℝ) := by
  have width_eq : (unitWidth:ℝ) = unitBin 1 := by norm_num [unitWidth,unitBin,Centres.w]
  have wpos : (0:ℝ) ≤ unitBin 1 := by norm_num [unitBin,Centres.w]
  have pilo : (333/106:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
  have row (i : Fin 16384) :
      (if b.condition (unitBin (i.val+1)) then
        (Packing.neighbourCap a (unitBin (i.val+1)):ℝ) * unitStep physical (i.val+1) else 0)
      ≤ (weightedRow rows b i:ℝ)/denom := by
    have k := Packing.neighbourCap_le_capUpper radiusR (unitT (i.val+1))
    rw [t_cast,show (radiusR:ℝ)=a by norm_num [radiusR,a,Centres.δR]] at k
    unfold weightedRow
    dsimp only
    by_cases cond : b.condition (unitBin (i.val+1))
    · rw [if_pos cond,if_pos ((used_iff b _).mpr cond),Int.cast_mul,Int.cast_natCast,mul_div_assoc,exactRows]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast k) (unitStep_nonneg (physical_sound W p) _)
    · rw [if_neg cond,if_neg (fun ok => cond ((used_iff b _).mp ok))]
      simp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row i)
  have nonneg : 0 ≤ ∑ i : Fin 16384, (weightedRow rows b i:ℝ)/denom := by
    apply Finset.sum_nonneg
    intro i _
    apply le_trans _ (row i)
    split
    · exact mul_nonneg (Nat.cast_nonneg _) (unitStep_nonneg (physical_sound W p) _)
    · exact le_rfl
  have low := div_le_div_of_nonneg_left wpos (by norm_num : (0:ℝ)<333/106) pilo
  unfold packingSum
  apply (mul_le_mul_of_nonneg_left hsum (div_nonneg wpos Real.pi_pos.le)).trans
  apply (mul_le_mul_of_nonneg_right low nonneg).trans_eq
  unfold packingUpper
  rw [← Array.sum_toList,Array.toList_ofFn,List.sum_ofFn]
  push_cast
  rw [width_eq,← Finset.sum_div]
  ring

end
end HadwigerNelson.Certificate.Hole
