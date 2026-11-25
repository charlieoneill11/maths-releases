import HadwigerNelson.Forest.FoldedAngles
import HadwigerNelson.Forest.BlankPairs
import HadwigerNelson.Arithmetic.Pi

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Centres
open scoped BigOperators
noncomputable section

private theorem arctan_secant_lower {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    (v-u)/(1+v^2) ≤ Real.arctan v - Real.arctan u := by
  rcases huv.eq_or_lt with rfl|lt
  · simp
  obtain ⟨t,ht,e⟩ := exists_deriv_eq_slope Real.arctan lt Real.continuous_arctan.continuousOn
    Real.differentiable_arctan.differentiableOn
  rw [Real.deriv_arctan] at e
  dsimp only at e
  have square := pow_le_pow_left₀ (hu.trans ht.1.le) ht.2.le 2
  have q := one_div_le_one_div_of_le (by positivity : (0:ℝ)<1+t^2) (by linarith : 1+t^2≤1+v^2)
  rw [e] at q
  have b := (le_div_iff₀ (sub_pos.mpr lt)).mp q
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using b

private theorem short_mean_lower {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {ρ : ℝ} (hρ : 0≤ρ) : lowerShortMean Ω ρ ≤ shortMean Ω ρ := by
  have nonneg (i : Fin 8192) : 0 ≤ cappedShort Ω ρ i :=
    le_min (short_nonneg sound hρ (by omega : i.val ≤ 8191)) (cap_nonneg sound hρ)
  have monotone (i : Fin 8192) : shortBin i ≤ shortBin (i.val+1) := by simp [shortBin]; linarith
  have each (i : Fin 8192) :
      2*(shortBin (i.val+1)-shortBin i)/(1+shortBin (i.val+1)^2) ≤
        2*Real.arctan (shortBin (i.val+1))-2*Real.arctan (shortBin i) := by
    have z := arctan_secant_lower (show 0≤shortBin i by unfold shortBin; positivity) (monotone i)
    rw [mul_div_assoc,← mul_sub]
    exact mul_le_mul_of_nonneg_left z (by norm_num)
  have πbound : Real.pi ≤ 355/113 := by linarith [Real.pi_lt_d20]
  unfold lowerShortMean shortMean
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left (by norm_num) Real.pi_pos πbound
  · apply Finset.sum_le_sum; intro i _; exact mul_le_mul_of_nonneg_left (each i) (nonneg i)
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (nonneg i) (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (monotone i))) (by positivity))
  · positivity

private theorem rotate_shortIndex (v : Plane) (hv : v≠0) :
    ∃ φ : ℝ, ∀ θ,shortIndex (rotate θ v)=foldedIndex 8192 (θ+φ) := by
  obtain ⟨φ,h⟩ := rotated_components v
  have hn := norm_pos_iff.mpr hv
  have rn (θ : ℝ) : ‖rotate θ v‖=‖v‖ := by
    have zero : rotate θ 0=0 := by ext i; fin_cases i <;> simp [rotate,Wave.point]
    simpa only [zero,dist_zero_right] using rotate_dist θ v 0
  refine ⟨φ,fun θ => ?_⟩
  unfold shortIndex foldedIndex
  rw [rn,h θ,Wave.point_fst,Wave.point_snd,abs_mul,abs_mul,abs_of_pos hn]
  congr 2
  push_cast
  have den : ‖v‖+‖v‖*|Real.cos (θ+φ)| = ‖v‖*(1+|Real.cos (θ+φ)|) := by ring
  rw [den]
  field_simp

theorem averaged_short_parent (W : Wave.Datum) (Ω : ℝ → ℝ → ℝ) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) (y : Plane) (hy : y∈X) (notRoot : y∉L.D) :
    let ρ := if y∈L.R then d else a
    lowerShortMean Ω ρ ≤ shortMean Ω ρ ∧
    (∫ θ,edgeShort L Ω .r θ y ∂uniformInterval (2*Real.pi)) = shortMean Ω ρ := by
  classical
  intro ρ
  have hρ : 0≤ρ := by dsimp only [ρ]; split <;> norm_num [a,d,δR,δ]
  obtain ⟨_,hn,_⟩ := parent_edge L hy notRoot
  obtain ⟨φ,ha⟩ := rotate_shortIndex (y-L.parent y) (sub_ne_zero.mpr hn)
  refine ⟨short_mean_lower sound hρ,?_⟩
  have trans (θ : ℝ) : edgeShort L Ω .r θ y=cappedShort Ω ρ (foldedIndex 8192 (θ+φ)) := by
    simp [edgeShort,notRoot,ρ,ha]
  simp_rw [trans]
  rw [folded_mean 8192 (by decide) (cappedShort Ω ρ) φ,← Fin.sum_univ_eq_sum_range]
  rfl

end
end HadwigerNelson.Forest
