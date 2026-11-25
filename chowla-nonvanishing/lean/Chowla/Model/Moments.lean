import Chowla.Model.Symmetry

namespace Chowla

open MeasureTheory MvPolynomial
open scoped BigOperators

noncomputable def listMoment (hs : List FourierProfile) : ℝ := modelMoment hs.get

/-- The cumulant of a block of labelled profiles. -/
noncomputable def blockCumulant {ι : Type*} [LinearOrder ι] (h : ι → FourierProfile)
    (B : Finset ι) : ℝ :=
  cumulant ((B.sort (· ≤ ·)).map h)

theorem blockCumulant_map {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (h : ι → FourierProfile) (g : κ → FourierProfile) (e : ι ↪ κ) (B : Finset ι)
    (he : ∀ u ∈ B, g (e u) = h u) (hh : ∀ u ∈ B, IsProfile (h u)) :
    blockCumulant h B = blockCumulant g (B.map e) := by
  have hp : ((B.sort (· ≤ ·)).map h).Perm (((B.map e).sort (· ≤ ·)).map g) := by
    rw [← Multiset.coe_eq_coe]
    simp only [← Multiset.map_coe, Finset.sort_eq, Finset.map_val, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i hi
    exact (he i hi).symm
  apply cumulant_perm hp
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
  exact hh i ((Finset.mem_sort (· ≤ ·)).mp hi)

private def finsetOrderIso {ι κ : Type*} (e : ι ≃ κ) : Finset ι ≃o Finset κ where
  toEquiv := e.finsetCongr
  map_rel_iff' := Finset.map_subset_map

/-- Relabelling a partition transports each block along the same equivalence. -/
noncomputable def finpartitionEquiv {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (B : Finset ι) : Finpartition B ≃ Finpartition (B.map e.toEmbedding) := by
  let o := finsetOrderIso e
  have h : o.symm (B.map e.toEmbedding) = B := o.symm_apply_apply B
  refine ⟨fun P => P.map o, fun Q => (Q.map o.symm).copy h, ?_, ?_⟩
  · intro P
    ext1
    change (P.parts.map o.toEquiv.toEmbedding).map o.toEquiv.symm.toEmbedding = P.parts
    rw [Finset.map_map]
    rw [show o.toEquiv.toEmbedding.trans o.toEquiv.symm.toEmbedding =
      Function.Embedding.refl (Finset ι) from Function.Embedding.ext fun X => o.symm_apply_apply X]
    exact Finset.map_refl
  · intro Q
    ext1
    change (Q.parts.map o.toEquiv.symm.toEmbedding).map o.toEquiv.toEmbedding = Q.parts
    rw [Finset.map_map]
    rw [show o.toEquiv.symm.toEmbedding.trans o.toEquiv.toEmbedding =
      Function.Embedding.refl (Finset κ) from Function.Embedding.ext fun X => o.apply_symm_apply X]
    exact Finset.map_refl

@[simp] theorem finpartitionEquiv_parts {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (B : Finset ι) (P : Finpartition B) :
    (finpartitionEquiv e B P).parts = P.parts.map e.finsetCongr.toEmbedding := rfl

noncomputable def partitionMoment {ι : Type*} [LinearOrder ι] (h : ι → FourierProfile)
    (B : Finset ι) : ℝ := by
  classical
  exact ∑ P : Finpartition B, ∏ s ∈ P.parts, blockCumulant h s

theorem partitionMoment_map {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (h : ι → FourierProfile) (g : κ → FourierProfile)
    (e : ι ≃ κ) (B : Finset ι) (he : ∀ i ∈ B, g (e i) = h i)
    (hh : ∀ i ∈ B, IsProfile (h i)) :
    partitionMoment h B = partitionMoment g (B.map e.toEmbedding) := by
  classical
  unfold partitionMoment
  refine Finset.sum_equiv (finpartitionEquiv e B) (fun _ => by simp) ?_
  intro P _
  rw [finpartitionEquiv_parts, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro s hs
  exact blockCumulant_map h g e.toEmbedding s (fun i hi => he i (P.le hs hi))
    (fun i hi => hh i (P.le hs hi))

private theorem exists_get_equiv {α : Type*} {l m : List α} (p : l.Perm m) :
    ∃ e : Fin l.length ≃ Fin m.length, ∀ i, m.get (e i) = l.get i := by
  induction p with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | @cons a l m p ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(finSuccEquiv l.length).trans ((Equiv.optionCongr e).trans (finSuccEquiv m.length).symm), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa only [Equiv.trans_apply, finSuccEquiv_succ, show ∀ z, (Equiv.optionCongr e) (some z) = some (e z) from fun _ => rfl,
        finSuccEquiv_symm_some, List.get_cons_succ] using he j
  | swap a b l =>
    let i₀ : Fin (l.length + 2) := 0
    let i₁ : Fin (l.length + 2) := Fin.succ 0
    let e := Equiv.swap i₀ i₁
    refine ⟨e, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · change (a :: b :: l).get (e i₀) = b
      have h : e i₀ = i₁ := Equiv.swap_apply_left _ _
      exact congrArg (a :: b :: l).get h
    · change (a :: b :: l).get (e i₁) = a
      have h : e i₁ = i₀ := Equiv.swap_apply_right _ _
      exact congrArg (a :: b :: l).get h
    · have hzero : k.succ.succ ≠ i₀ := Fin.succ_ne_zero _
      have hone : k.succ.succ ≠ i₁ := fun h => Fin.succ_ne_zero k (Fin.succ_inj.mp h)
      have h : e k.succ.succ = k.succ.succ := Equiv.swap_apply_of_ne_of_ne hzero hone
      exact congrArg (a :: b :: l).get h
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂
    exact ⟨e.trans f, fun i => (hf (e i)).trans (he i)⟩

theorem listMoment_perm {hs gs : List FourierProfile} (hp : hs.Perm gs)
    (hh : ∀ h ∈ hs, IsProfile h) : listMoment hs = listMoment gs := by
  obtain ⟨e, he⟩ := exists_get_equiv hp
  have h := partitionMoment_map hs.get gs.get e Finset.univ (fun i _ => he i)
    (fun i _ => hh _ (List.get_mem _ _))
  rw [Finset.map_univ_equiv] at h
  exact h

noncomputable def modelExpectationLinear : Model →ₗ[ℝ] ℝ :=
  Finsupp.lift ℝ ℝ (FourierProfile →₀ ℕ) (fun m => listMoment m.toMultiset.toList)

theorem modelExpectation_eq_linear (P : Model) : modelExpectation P = modelExpectationLinear P := by
  rfl

private noncomputable def powersOfList (hs : List FourierProfile) : FourierProfile →₀ ℕ := by
  classical
  exact (hs : Multiset FourierProfile).toFinsupp

private theorem stat_prod_eq_monomial (hs : List FourierProfile) :
    (hs.map stat).prod = monomial (powersOfList hs) 1 := by
  classical
  unfold powersOfList
  induction hs with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Multiset.coe_nil, Multiset.toFinsupp_zero,
      MvPolynomial.one_def]
  | cons h hs ih =>
    rw [List.map_cons, List.prod_cons, ih, stat, MvPolynomial.X, monomial_mul, one_mul,
      ← Multiset.toFinsupp_singleton h, ← Multiset.toFinsupp_add, Multiset.singleton_add]
    rfl

/-- Model expectation agrees with the moment of each monomial in the formal generators. -/
theorem modelExpectation_monomial_of_isProfile (hs : List FourierProfile)
    (hhs : ∀ h ∈ hs, IsProfile h) :
    modelExpectation ((hs.map stat).prod) = listMoment hs := by
  classical
  rw [stat_prod_eq_monomial, powersOfList, modelExpectation, support_monomial, if_neg one_ne_zero,
    Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul, Multiset.toFinsupp_toMultiset]
  apply listMoment_perm
  · exact Multiset.coe_eq_coe.mp (Multiset.coe_toList _)
  · intro h hh
    exact hhs h (by simpa using hh)

/-- The monomial identity for generators in the model algebra of Section 4.1. -/
theorem modelExpectation_monomial (hs : List FourierProfile)
    (hhs : ∀ h ∈ hs, IsProfile h ∧ ContinuousAt h 0) :
    modelExpectation ((hs.map stat).prod) = listMoment hs :=
  modelExpectation_monomial_of_isProfile hs (fun h hh => (hhs h hh).1)

end Chowla
