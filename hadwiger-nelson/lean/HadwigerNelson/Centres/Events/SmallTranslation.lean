import HadwigerNelson.Centres.Events.RectangleArea
import HadwigerNelson.Placement.HoleTranslations

namespace HadwigerNelson.Centres
open Set MeasureTheory Wave Placement

theorem angleBin_eq {p : Profile} {l t : ℝ} (step : 0<angleStep p l)
    (j : Fin (angleBins p)) (left : (j.val:ℝ)*angleStep p l < |t|)
    (right : |t|≤((j.val:ℝ)+1)*angleStep p l) : angleBin p l t = j.val+1 := by
  have h : ⌈|t|/angleStep p l⌉₊ = j.val+1 := by
    apply (Nat.ceil_eq_iff (by omega)).mpr
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    exact ⟨(lt_div_iff₀ step).2 left,(div_le_iff₀ step).2 right⟩
  rw [angleBin,h,min_eq_right (by omega),max_eq_right (by omega)]

/-- The true area of the small-chord midpoint strips gives a lower bound
on the probability of the selected translations at this fixed rotation. -/
theorem small_translation_bound (W : Datum) (X D : Finset Plane) (p : Profile)
    (θ t : ℝ) (v u : Plane) (hc : candidate X D p θ v u)
    (small : chord u v ≤ 2/100) (ht : |t|≤cone p (chord u v)) (a : aligned θ t v u)
    (step : 0≤angleStep p (chord u v)) :
    (4*heightStep p/(2*W.x*H))*
      (∑ k : Fin (heightBins p), rectangleHalfWidth W p (chord u v)
        (angleBin p (chord u v) t) k.val) ≤ (translationLaw W).real (centreEvent W X D p θ v u) := by
  let B := smallRegion W p (chord u v) t
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  have area := smallRegion_area W p (chord u v) t step
  have probability := translate_probability_lower W B (rotate θ (midpoint u v)) (centreEvent W X D p θ v u)
    (smallRegion_measurable ..)
    (source_packing W B (fun _ hit => region_bounds W p _ _ step hit))
    (by
      intro τ g hz
      obtain ⟨i,j,eg⟩ := (mem_holeLattice W g).mp g.2
      refine ⟨hc,i,j,?_⟩
      dsimp only
      rw [if_pos small]
      refine ⟨t,ht,a,?_⟩
      rw [eg] at hz
      simpa only [place,translationPoint,add_comm] using hz)
  refine (le_of_eq ?_).trans ((div_le_div_of_nonneg_right area (by have := H_pos; positivity : (0:ℝ)≤2*W.x*H)).trans probability)
  ring

end HadwigerNelson.Centres
