import Chowla.CountingMassClasses
import Chowla.CountingMassConstant
import Chowla.CountingSmoothMass

namespace Chowla

open Filter MeasureTheory
open scoped BigOperators Topology

private theorem tendsto_squarefree_residue_density (r : ℕ) (hr : r = 1 ∨ r = 3) :
    Tendsto (fun X : ℝ => ((squarefreeResidueClassFour r X).card : ℝ) / X) atTop
      (𝓝 (2 / Real.pi^2)) := by
  have h := tendsto_squarefreeResidueClassFour_card r hr
  rw [oddMoebiusTerm_tsum, show (8 / Real.pi^2) / 4 = 2 / Real.pi^2 by ring] at h
  exact h

private theorem odd_of_residue_eq {m r : ℕ} (hr : r = 1 ∨ r = 3) (h : m % 4 = r) :
    Odd m := Nat.odd_iff.mpr (Nat.odd_mod_four_iff.mpr (h ▸ hr))

private def signResidue (s : DiscSign) : ℕ :=
  match s with
  | .positive => 1
  | .negative => 3

private theorem signResidue_odd (s : DiscSign) : signResidue s = 1 ∨ signResidue s = 3 := by
  cases s <;> decide

private theorem signedCore_one_mod_four (s : DiscSign) (m : ℕ) :
    (s.value * (m : ℤ)) % 4 = 1 ↔ m % 4 = signResidue s := by
  cases s <;> simp only [DiscSign.value, signResidue, one_mul, neg_one_mul] <;> omega

private theorem signedCore_three_mod_four (s : DiscSign) (m : ℕ) :
    (s.value * (m : ℤ)) % 4 = 3 ↔ m % 4 = 4 - signResidue s := by
  cases s <;> simp only [DiscSign.value, signResidue, one_mul, neg_one_mul] <;> omega

private theorem signResidue_other_odd (s : DiscSign) :
    4 - signResidue s = 1 ∨ 4 - signResidue s = 3 := by
  cases s <;> decide

private theorem classCoreCutoff_odd (s : DiscSign) (X : ℝ) :
    classCoreCutoff (s, .odd) X = (squarefreeResidueClassFour (signResidue s) X).erase 1 := by
  classical
  ext m
  simp only [classCoreCutoff, ClassCorePred, squarefreeResidueClassFour, residueClassFour,
    Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, signedCore_one_mod_four]
  constructor
  · rintro ⟨hb, _, hsq, hm, hmod⟩
    exact ⟨hm.ne', ⟨hb, hmod⟩, hsq⟩
  · rintro ⟨hne, ⟨hb, hmod⟩, hsq⟩
    exact ⟨hb, odd_of_residue_eq (signResidue_odd s) hmod, hsq, by omega, hmod⟩

private theorem classCoreCutoff_four (s : DiscSign) (X : ℝ) :
    classCoreCutoff (s, .four) X = squarefreeResidueClassFour (4 - signResidue s) X := by
  classical
  ext m
  simp only [classCoreCutoff, ClassCorePred, squarefreeResidueClassFour, residueClassFour,
    Finset.mem_filter, Finset.mem_Icc, signedCore_three_mod_four]
  constructor
  · rintro ⟨hb, _, hsq, hmod⟩
    exact ⟨⟨hb, hmod⟩, hsq⟩
  · rintro ⟨⟨hb, hmod⟩, hsq⟩
    exact ⟨hb, odd_of_residue_eq (signResidue_other_odd s) hmod, hsq, hmod⟩

private theorem classCoreCutoff_eight (s : DiscSign) (X : ℝ) :
    classCoreCutoff (s, .eight) X =
      squarefreeResidueClassFour 1 X ∪ squarefreeResidueClassFour 3 X := by
  classical
  ext m
  simp only [classCoreCutoff, ClassCorePred, squarefreeResidueClassFour, residueClassFour,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, and_true, Nat.odd_iff,
    Nat.odd_mod_four_iff]
  tauto

private theorem classCoreCutoff_eight_disjoint (X : ℝ) :
    Disjoint (squarefreeResidueClassFour 1 X) (squarefreeResidueClassFour 3 X) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₃
  simp only [squarefreeResidueClassFour, residueClassFour, Finset.mem_filter] at hn₁ hn₃
  omega

private theorem tendsto_card_erase_one {S : ℝ → Finset ℕ} {c : ℝ}
    (h : Tendsto (fun X => ((S X).card : ℝ) / X) atTop (𝓝 c)) :
    Tendsto (fun X => (((S X).erase 1).card : ℝ) / X) atTop (𝓝 c) := by
  classical
  have hlow : Tendsto (fun X => ((S X).card : ℝ) / X - X⁻¹) atTop (𝓝 c) := by
    simpa only [sub_zero] using h.sub tendsto_inv_atTop_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow h ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hcard : (S X).card ≤ ((S X).erase 1).card + 1 := by
      by_cases hx : 1 ∈ S X
      · exact (Finset.card_erase_add_one hx).symm.le
      · rw [Finset.erase_eq_of_notMem hx]
        exact Nat.le_succ _
    have hc : ((S X).card : ℝ) ≤ (((S X).erase 1).card : ℝ) + 1 := by exact_mod_cast hcard
    rw [← one_div, ← sub_div, div_le_div_iff_of_pos_right hX]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card (Finset.erase_subset _ _)))
      hX.le

/-- Prefix density for the positive odd parameter in every discriminant class. -/
theorem tendsto_classCoreCutoff_card (D : DiscClass) :
    Tendsto (fun X : ℝ => ((classCoreCutoff D X).card : ℝ) / X) atTop
      (𝓝 (classDensity D)) := by
  obtain ⟨s, t⟩ := D
  cases t with
  | odd =>
    simpa only [classCoreCutoff_odd, classDensity] using
      tendsto_card_erase_one (tendsto_squarefree_residue_density (signResidue s) (signResidue_odd s))
  | four =>
    simpa only [classCoreCutoff_four, classDensity] using
      tendsto_squarefree_residue_density (4 - signResidue s) (signResidue_other_odd s)
  | eight =>
    have h := (tendsto_squarefree_residue_density 1 (.inl rfl)).add
      (tendsto_squarefree_residue_density 3 (.inr rfl))
    rw [show 2 / Real.pi^2 + 2 / Real.pi^2 = classDensity (s, .eight) by simp only [classDensity]; ring] at h
    apply h.congr'
    exact Filter.Eventually.of_forall fun X => by
      dsimp only
      rw [classCoreCutoff_eight, Finset.card_union_of_disjoint (classCoreCutoff_eight_disjoint X),
        Nat.cast_add, add_div]

private theorem tendsto_discriminant_prefix_card (D : DiscClass) :
    Tendsto (fun X : ℝ => ((classDiscs D ((D.2.kappa : ℝ) * X)).card : ℝ) / X)
      atTop (𝓝 (classDensity D)) := by
  apply (tendsto_classCoreCutoff_card D).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  rw [classDiscs_card_eq_core D hX]

theorem tendsto_sharpShell_card (D : DiscClass) :
    Tendsto (fun X : ℝ => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D)) := by
  have hprefix := tendsto_discriminant_prefix_card D
  have hscale : Tendsto (fun X : ℝ => 2 * X) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have h := ((hprefix.comp hscale).const_mul (2 : ℝ)).sub hprefix
  rw [show 2 * classDensity D - classDensity D = classDensity D by ring] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hcut : 2 * (D.2.kappa : ℝ) * X = (D.2.kappa : ℝ) * (2 * X) := by ring
  have hsubset : classDiscs D ((D.2.kappa : ℝ) * X) ⊆
      classDiscs D ((D.2.kappa : ℝ) * (2 * X)) := by
    apply classDiscs_mono D
    apply mul_le_mul_of_nonneg_left (by linarith) (kappa_pos D).le
  rw [sharpShell_eq_sdiff, hcut, Finset.cast_card_sdiff hsubset]
  simp only [Function.comp_apply]
  field_simp [hX.ne']

theorem tendsto_weightedMass (D : DiscClass) (W : ShellWeight) :
    Tendsto (fun X : ℝ => weightedSum D W X (fun _ => 1) / X) atTop
      (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)) := by
  classical
  have h := weightedSum_tendsto_of_prefix W (ClassCorePred D) (classDensity D)
    (by simpa only [classCoreCutoff] using tendsto_classCoreCutoff_card D)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  simp only [weightedMass_eq_core D W hX, classCoreCutoff]

/-- Lemma 8 for the empty local pattern, with both smooth and sharp shell masses. -/
theorem squarefree_shell_mass (D : DiscClass) (W : ShellWeight) :
    Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
      (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)) ∧
    Tendsto (fun X : ℝ => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D)) :=
  ⟨tendsto_weightedMass D W, tendsto_sharpShell_card D⟩

end Chowla
