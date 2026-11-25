import Chowla.Amplitude
import Chowla.Model.Contraction
import Chowla.Model.MatchingLinear
import Chowla.Model.RowCumulant

namespace Chowla

open MeasureTheory
open scoped BigOperators

noncomputable def Row.scale (c : ℝ) (k : Row) : Row :=
  ⟨k.widths, fun u => c * k.profile u⟩

theorem Row.Admissible.scale {k : Row} (hk : k.Admissible) (c : ℝ) :
    (k.scale c).Admissible := by
  have hs := (hasRadiusAtMost_radius hk.2.1).mono hk.2.2.2
  refine ⟨hk.1, hk.2.1.const_mul c, ?_, radius_le_of_hasRadiusAtMost (hs.const_mul c)⟩
  change (∫ u : ℝ, c * k.profile u) = 0
  rw [integral_const_mul, hk.2.2.1, mul_zero]

theorem innerRow_eq_crossMatchingSum (k l : Row) (hk : k.Admissible) (hl : l.Admissible) :
    innerRow k l = crossMatchingSum (convolve k.profile l.profile) k.widths l.widths := by
  apply contraction_formula_of_profile
  · exact convolve_isProfile hk.2.1 hl.2.1
  · exact ⟨hk.1, by linarith [hk.2.2.2, radius_nonneg hk.2.1]⟩
  · exact ⟨hl.1, by linarith [hl.2.2.2, radius_nonneg hl.2.1]⟩
  · linarith [radius_convolve_le hk.2.1 hl.2.1, hk.2.2.2, hl.2.2.2]

theorem innerRow_scale_left (k l : Row) (hk : k.Admissible) (hl : l.Admissible) (c : ℝ) :
    innerRow (k.scale c) l = c * innerRow k l := by
  rw [innerRow_eq_crossMatchingSum _ _ (hk.scale c) hl,
    innerRow_eq_crossMatchingSum _ _ hk hl]
  change crossMatchingSum (convolve (fun u => c * k.profile u) l.profile) k.widths l.widths = _
  rw [convolve_const_mul_head, crossMatchingSum_const_mul]

theorem innerRow_add_profile (k k₁ k₂ l : Row) (hk : k.Admissible)
    (hk₁ : k₁.Admissible) (hk₂ : k₂.Admissible) (hl : l.Admissible)
    (h₁ : k₁.widths = k.widths) (h₂ : k₂.widths = k.widths)
    (h : k.profile = k₁.profile + k₂.profile) :
    innerRow k l = innerRow k₁ l + innerRow k₂ l := by
  rw [innerRow_eq_crossMatchingSum _ _ hk hl, innerRow_eq_crossMatchingSum _ _ hk₁ hl,
    innerRow_eq_crossMatchingSum _ _ hk₂ hl, h₁, h₂, h,
    convolve_add_head hk₁.2.1 hk₂.2.1 (integrable_of_isProfile hl.2.1),
    crossMatchingSum_add (convolve_isProfile hk₁.2.1 hl.2.1) (convolve_isProfile hk₂.2.1 hl.2.1)]

theorem innerGRow_scale (k : Row) (hk : k.Admissible) (c : ℝ) :
    innerGRow (k.scale c) = c * innerGRow k := by
  by_cases h : k.widths = []
  · rw [innerGRow_nil _ (hk.scale c) h, innerGRow_nil _ hk h, mul_zero]
  · rw [innerGRow_eq_cumulant _ (hk.scale c) h, innerGRow_eq_cumulant _ hk h]
    change cumulant (convolve H (fun u => c * k.profile u) :: k.widths.map rectangle) = _
    rw [convolve_const_mul_right, cumulant_const_mul_head]

theorem inner_G_scale (F : Amplitude) (hF : IsAmplitude F) (c : ℝ) :
    inner_G (F.map (Row.scale c)) = c * inner_G F := by
  induction F with
  | nil => simp [inner_G]
  | cons k F ih =>
    have htail : IsAmplitude F := fun f hf => hF f (List.mem_cons_of_mem _ hf)
    simp only [inner_G, List.map_cons, List.sum_cons]
    have ht := ih htail
    unfold inner_G at ht
    rw [innerGRow_scale k (hF k (by simp)) c, ht, mul_add]

theorem inner_scale_left (F F' : Amplitude) (hF : IsAmplitude F) (hF' : IsAmplitude F') (c : ℝ) :
    inner (F.map (Row.scale c)) F' = c * inner F F' := by
  have hrow (k : Row) (hk : k.Admissible) :
      (F'.map (innerRow (k.scale c))).sum = c * (F'.map (innerRow k)).sum := by
    induction F' with
    | nil => simp
    | cons l F' ih =>
      have htail : IsAmplitude F' := fun f hf => hF' f (List.mem_cons_of_mem _ hf)
      simp only [List.map_cons, List.sum_cons]
      rw [innerRow_scale_left k l hk (hF' l (by simp)) c, ih htail, mul_add]
  induction F with
  | nil => simp [inner]
  | cons k F ih =>
    have htail : IsAmplitude F := fun f hf => hF f (List.mem_cons_of_mem _ hf)
    simp only [inner, List.map_cons, List.sum_cons]
    have ht := ih htail
    unfold inner at ht
    rw [hrow k (hF k (by simp)), ht, mul_add]

theorem inner_scale_self (F : Amplitude) (hF : IsAmplitude F) (c : ℝ) :
    inner (F.map (Row.scale c)) (F.map (Row.scale c)) = c^2 * inner F F := by
  have hscaled : IsAmplitude (F.map (Row.scale c)) := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    exact (hF r hr).scale c
  rw [inner_scale_left F _ hF hscaled, inner_comm F, inner_scale_left F F hF hF]
  ring

end Chowla
