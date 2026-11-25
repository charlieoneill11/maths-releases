import Chowla.Model.Cumulants
import Mathlib.LinearAlgebra.Finsupp.LSum

namespace Chowla

open Filter MeasureTheory
open scoped BigOperators Convolution

private def ConvolutionInput (h : FourierProfile) : Prop :=
  Integrable h ∧ ∃ C : ℝ, ∀ u : ℝ, |h u| ≤ C

private theorem convolutionInput_of_isProfile {h : FourierProfile} (hh : IsProfile h) :
    ConvolutionInput h := by
  refine ⟨integrable_of_isProfile hh, ?_⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hh.2.2.1
  exact ⟨C, fun u => by simpa only [Real.norm_eq_abs] using hC (h u) ⟨u, rfl⟩⟩

private theorem ConvolutionInput.oddProfile {h : FourierProfile} (hh : ConvolutionInput h)
    (hm : Measurable h) : ConvolutionInput (oddProfile h) := by
  obtain ⟨C, hC⟩ := hh.2
  exact ⟨integrable_oddProfile hm hh.1, C, fun u => (abs_oddProfile_le h u).trans (hC u)⟩

private theorem ConvolutionInput.convolve {h g : FourierProfile}
    (hh : ConvolutionInput h) (hg : ConvolutionInput g) : ConvolutionInput (convolve h g) := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨integrable_convolve hh.1 hg.1, profileL1 h * C, abs_convolve_le_of_right_bound hh.1 hC⟩

private theorem convolutionInput_convolutionList {hs : List FourierProfile}
    (hh : ∀ h ∈ hs, ConvolutionInput h) : ConvolutionInput (convolutionList hs) := by
  induction hs with
  | nil =>
    change ConvolutionInput 0
    exact ⟨integrable_zero _ _ _, 0, by simp⟩
  | cons h hs ih =>
    have hh' := hh h List.mem_cons_self
    cases hs with
    | nil => exact hh'
    | cons g gs => exact hh'.convolve (ih fun u hu => hh u (List.mem_cons_of_mem h hu))

theorem convolve_assoc_of_bound {h g k : FourierProfile}
    (hh : Integrable h) (hg : Integrable g) (hk : Integrable k)
    {C : ℝ} (hC : ∀ u : ℝ, |k u| ≤ C) :
    convolve (convolve h g) k = convolve h (convolve g k) := by
  funext u
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hk' : AEStronglyMeasurable (fun p : ℝ × ℝ => k (u - p.1)) (volume.prod volume) :=
    (hk.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume u)).comp_fst
  have hprod : Integrable (fun p : ℝ × ℝ => h p.2 * g (p.1 - p.2) * k (u - p.1)) (volume.prod volume) :=
    (hh.convolution_integrand L hg).mul_bdd hk'
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hC (u - p.1))
  apply convolution_assoc' L L L L (fun x y z => by
    simp only [L, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_assoc])
    (hh.ae_convolution_exists L hg) (hg.ae_convolution_exists L hk)
  simpa only [L, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Function.uncurry, mul_assoc] using hprod

private theorem convolve_assoc_of_input {h g k : FourierProfile}
    (hh : ConvolutionInput h) (hg : ConvolutionInput g) (hk : ConvolutionInput k) :
    convolve (convolve h g) k = convolve h (convolve g k) := by
  obtain ⟨C, hC⟩ := hk.2
  exact convolve_assoc_of_bound hh.1 hg.1 hk.1 hC

private theorem convolutionList_perm {hs gs : List FourierProfile} (hp : hs.Perm gs)
    (hh : ∀ h ∈ hs, ConvolutionInput h) : convolutionList hs = convolutionList gs := by
  induction hp with
  | nil => rfl
  | @cons h a b hp ih =>
    have ht : ∀ t ∈ a, ConvolutionInput t := fun t ht => hh t (List.mem_cons_of_mem h ht)
    cases a with
    | nil =>
      rw [List.nil_perm.mp hp]
    | cons a as =>
      cases b with
      | nil => simp at hp
      | cons b bs => exact congrArg (convolve h) (ih ht)
  | swap g h hs =>
    cases hs with
    | nil => exact convolve_comm h g
    | cons k ks =>
      have hh' := hh h (by simp)
      have hg' := hh g (by simp)
      have hk' := convolutionInput_convolutionList fun t ht =>
        hh t (List.mem_cons_of_mem h (List.mem_cons_of_mem g ht))
      change convolve h (convolve g (convolutionList (k :: ks))) =
        convolve g (convolve h (convolutionList (k :: ks)))
      rw [← convolve_assoc_of_input hh' hg' hk', convolve_comm h g,
        convolve_assoc_of_input hg' hh' hk']
  | trans hab _ ihab ihbc =>
    exact (ihab hh).trans (ihbc fun t ht => hh t (hab.mem_iff.mpr ht))

theorem delta_perm {hs gs : List FourierProfile} (hp : hs.Perm gs)
    (hh : ∀ h ∈ hs, IsProfile h) : delta hs = delta gs := by
  have hconv : convolutionList (hs.map oddProfile) = convolutionList (gs.map oddProfile) := by
    apply convolutionList_perm (hp.map oddProfile)
    intro j hj
    obtain ⟨h, hmem, rfl⟩ := List.mem_map.mp hj
    exact (convolutionInput_of_isProfile (hh h hmem)).oddProfile (hh h hmem).1
  unfold delta
  rw [hp.length_eq, hconv]

theorem cumulant_pair_comm (h g : FourierProfile) (hh : IsProfile h) (hg : IsProfile g) :
    cumulant [h, g] = cumulant [g, h] := by
  simp only [cumulant]
  rw [delta_perm (List.Perm.swap g h []) (by simpa using And.intro hh hg)]
  congr 3 with u
  ring

theorem cumulant_perm {hs gs : List FourierProfile} (hp : hs.Perm gs)
    (hh : ∀ h ∈ hs, IsProfile h) : cumulant hs = cumulant gs := by
  cases hs with
  | nil => rw [List.nil_perm.mp hp]
  | cons h hs =>
    cases hs with
    | nil => rw [List.perm_singleton.mp hp.symm]
    | cons g hs =>
      cases hs with
      | nil =>
        obtain ⟨g', gs, rfl⟩ := List.exists_cons_of_ne_nil (show gs ≠ [] from by
          rintro rfl
          simp at hp)
        obtain ⟨h', gs, rfl⟩ := List.exists_cons_of_ne_nil (show gs ≠ [] from by
          rintro rfl
          have hlen := hp.length_eq
          simp at hlen)
        have hgs : gs = [] := by
          have hlen := hp.length_eq
          simp at hlen
          exact hlen
        subst gs
        have hh' := hh h (by simp)
        have hg' := hh g (by simp)
        have he : g' = h ∨ g' = g := by simpa using hp.mem_iff.mpr (by simp : g' ∈ [g', h'])
        rcases he with he | he
        · subst g'
          have heq : g = h' := List.singleton_perm_singleton.mp hp.cons_inv
          rw [heq]
        · subst g'
          have hp' := (List.Perm.swap h g []).trans hp
          have heq : h = h' := List.singleton_perm_singleton.mp hp'.cons_inv
          rw [← heq]
          exact cumulant_pair_comm _ _ hh' hg'
      | cons k ks =>
        cases gs with
        | nil => simp at hp
        | cons h' gs =>
          cases gs with
          | nil =>
            have hlen := hp.length_eq
            simp at hlen
          | cons g' gs =>
            cases gs with
            | nil =>
              have hlen := hp.length_eq
              simp at hlen
            | cons k' ks' => exact delta_perm hp hh

end Chowla
