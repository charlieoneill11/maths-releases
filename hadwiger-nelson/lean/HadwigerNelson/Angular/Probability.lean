import HadwigerNelson.Angular.PhysicalSlice
import HadwigerNelson.Angular.PhysicalBox
import HadwigerNelson.Angular.Weights
import HadwigerNelson.Angular.Normalize
import HadwigerNelson.Placement.Proposition12
import HadwigerNelson.Placement.Bin
import Mathlib.Analysis.Real.Pi.Bounds

namespace HadwigerNelson.Angular
open Wave Placement Arithmetic MeasureTheory Set

noncomputable section

private abbrev S : ℝ := CompleteWave.scale
private abbrev tree := tabulate CompleteWave.profile CompleteWave.step 11 0

private theorem Spos : (0:ℝ)<S := by norm_num [S,CompleteWave.scale]

private def physArea (n j : Nat) : ℝ :=
  (boxArea tree (halfAngleBox n j (j+1)) : ℝ)/(2*S^2)

private theorem physArea_nonneg (n j : Nat) : 0 ≤ physArea n j := by
  apply div_nonneg _ (by positivity)
  simp only [boxArea,Int.cast_add]
  exact add_nonneg (scaled_nonneg _ _ (ylo_nonneg ..)) (scaled_nonneg _ _ (shiftY_nonneg _))

private theorem cover {n j : Nat} (hn : 0<n) (hj : j<n) {θ : ℝ}
    (hθ : θ ∈ Icc (binEdge n j) (binEdge n (j+1))) :
    completeDatum.x*H*directionalMonoProb completeDatum (point (Real.cos θ) (Real.sin θ)) ≤ physArea n j := by
  let b := halfAngleBox n j (j+1)
  obtain ⟨cx,cy⟩ := bin_component_bounds hn hj hθ
  obtain ⟨hx,hy⟩ := box_encloses_components hn hj cx cy
  have r0 : (0:ℝ) ≤ Real.cos θ := by
    apply le_trans _ cx.1
    unfold rayX
    have h : ((j:ℝ)+1)/n ≤ 1 := (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast hj)
    have z : 0 ≤ ((j:ℝ)+1)/n := by positivity
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 1+((j:ℝ)+1)/n by linarith)]
  have s0 : (0:ℝ) ≤ Real.sin θ := by
    apply le_trans _ cy.1
    unfold rayY
    positivity
  have yl : 0 ≤ (b.ylo:ℝ)/S := div_nonneg (by exact_mod_cast ylo_nonneg n j (j+1)) Spos.le
  have h := monoProb_box completeDatum ⟨r0,Real.cos_le_one _⟩ ⟨s0,Real.sin_le_one _⟩ hx hy yl
  apply h.trans
  change _ ≤ (boxArea tree b:ℝ)/(2*S^2)
  unfold boxArea
  rw [Int.cast_add,add_div]
  apply add_le_add (physical_slice _ _ _ (ylo_nonneg ..))
  rw [completeDatum_x,shiftX_scaled]
  unfold reflectedLow
  rw [shiftY_scaled]
  exact physical_slice _ _ _ (shiftY_nonneg _)

/-- Proposition 12 applied to the specified complete profile using integer
bin totals and Mathlib's strictly lower 20-place rational bound for π. -/
theorem complete_probability_of_sum
    (checked : angularSum CompleteWave.profile (2^28) ≤ completeTotal) :
    meanMonoProb completeDatum ≤ (completeUpper:ℝ) := by
  let n := 2^28
  have hn : 0 < n := by decide
  have initial := meanMonoProb_of_bins completeDatum n hn (physArea n)
    (fun j _ => physArea_nonneg n j) (fun _ hj _ hθ => cover hn hj hθ)
  have exactSum :
      (∑ j ∈ Finset.range n, physArea n j*(2*(n:ℝ)/((n:ℝ)^2+(j:ℝ)^2))) =
        (∑ j ∈ Finset.range n,
          (boxArea tree (halfAngleBox n j (j+1)):ℝ)*n/((n:ℝ)*n+(j:ℝ)*j))/S^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [physArea]
    simp only [pow_two]
    ring
  rw [exactSum] at initial
  have aw := angular_weight_bound CompleteWave.profile hn (by decide : 4096 ∣ 2^28)
  have hupper : ((angularSum CompleteWave.profile n : Nat):ℝ) ≤ completeTotal := by exact_mod_cast checked
  have xh : 0 < completeDatum.x := by linarith [completeDatum.x_bounds.1]
  have plen : 0 ≤ 2/(Real.pi*completeDatum.x*H) :=
    div_nonneg (by norm_num) (mul_nonneg (mul_nonneg Real.pi_pos.le xh.le) H_pos.le)
  have w := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (aw.trans hupper) (sq_nonneg S)) plen
  apply (initial.trans w).trans
  have pLo : (314159265358979323846:ℝ)/10^20 < Real.pi := by
    linarith only [Real.pi_gt_d20]
  rw [completeDatum_x]
  simpa only [S,CompleteWave.xInt,CompleteWave.scale,H,Nat.cast_pow,Nat.cast_ofNat] using
    normalize_probability pLo.le

end
end HadwigerNelson.Angular
