import HadwigerNelson.Packing.Parameters
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Real

namespace HadwigerNelson.Packing
open MeasureTheory Finset Set Metric
noncomputable section

/-- Compare disjoint radius-ρ discs with the enclosing radius-(R+ρ) disc.
The centre z need not belong to the packed set. -/
theorem disks (P : Finset Plane) (z : Plane) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R)
    (sep : separated P (2*ρ)) (inside : ∀ x ∈ P, dist x z ≤ R) :
    (P.card:ℝ) ≤ (1+R/ρ)^2 := by
  let B (y : Plane) := ball y ρ
  have dis : Set.PairwiseDisjoint (P : Set Plane) B := by
    intro a ha b hb ne
    apply Set.disjoint_left.mpr
    intro p hp hq
    have hpa : dist p a < ρ := hp
    have hpb : dist p b < ρ := hq
    linarith [sep a ha b hb ne,dist_triangle_left a b p]
  have contained : (⋃ x ∈ P, B x) ⊆ ball z (R+ρ) := by
    intro p hp
    obtain ⟨x,hx,hp⟩ := Set.mem_iUnion₂.mp hp
    have hpx : dist p x < ρ := hp
    change dist p z < R+ρ
    linarith [dist_triangle p x z,inside x hx]
  let b := (volume : Measure Plane).real (ball 0 1)
  have pos : 0 < b := ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num : (0:ℝ)<1)).ne' measure_ball_lt_top.ne
  have area (c : Plane) (r : ℝ) (hr : 0 < r) : (volume : Measure Plane).real (ball c r) = r^2*b := by
    rw [Measure.real,Measure.addHaar_ball_of_pos volume c hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp only [finrank_euclideanSpace_fin]; rfl
  have count := measureReal_mono (μ := (volume : Measure Plane)) contained measure_ball_lt_top.ne
  rw [measureReal_biUnion_finset dis (fun x _ ↦ measurableSet_ball),area _ _ (by linarith)] at count
  have each (x : Plane) : (volume : Measure Plane).real (B x) = ρ^2*b := area _ _ hρ
  simp_rw [each] at count
  rw [Finset.sum_const,nsmul_eq_mul,←mul_assoc] at count
  have h := (mul_le_mul_iff_left₀ pos).mp count
  have eq : (1+R/ρ)^2 = (R+ρ)^2/ρ^2 := by field_simp [hρ.ne']; ring
  rw [eq]; exact (le_div_iff₀ (sq_pos_of_pos hρ)).mpr h

end
end HadwigerNelson.Packing
