import Chowla.VariationalPolynomial

namespace Chowla

open MvPolynomial
open scoped BigOperators SchwartzMap

private noncomputable def wickBlockPolynomial : List MomentTest → MomentPolynomial
  | [f] => MomentPolynomial.atom f ++ MomentPolynomial.const (-cumulant [f.profile])
  | [f, g] => MomentPolynomial.const (-cumulant [f.profile, g.profile])
  | _ => MomentPolynomial.const 1

noncomputable def wickPolynomial (L : List MomentTest) : MomentPolynomial := by
  classical
  let parts := (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin L.length)))).filter
    (fun π => ∀ B ∈ π.parts, B.card ≤ 2)
  exact MomentPolynomial.sum (parts.toList.map fun π =>
    MomentPolynomial.prod (π.parts.toList.map fun B =>
      wickBlockPolynomial ((B.sort (· ≤ ·)).map L.get)))

noncomputable def wickStatistic (L : List MomentTest) (X : ℝ) (d : ℤ) : ℝ :=
  (wickPolynomial L).statistic X d

private theorem wickBlockPolynomial_model (L : List MomentTest) :
    (wickBlockPolynomial L).model =
      match L.map MomentTest.profile with
      | [h] => centered h
      | [h, g] => C (-cumulant [h, g])
      | _ => 1 := by
  rw [← MomentPolynomial.eval_model]
  rcases L with _ | ⟨f, _ | ⟨g, _ | ⟨h, hs⟩⟩⟩ <;>
    simp [wickBlockPolynomial, MomentPolynomial.eval_append, centered, sub_eq_add_neg]

/-- The numerical Wick polynomial and the formal Wick polynomial use the same words. -/
theorem wickPolynomial_model (L : List MomentTest) :
    (wickPolynomial L).model = wick (L.map MomentTest.profile) := by
  classical
  let hs := L.map MomentTest.profile
  let Wick := fun {n : ℕ} (h : Fin n → FourierProfile) =>
    ∑ π ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n)))).filter
      (fun π => ∀ B ∈ π.parts, B.card ≤ 2),
      ∏ B ∈ π.parts,
        match (B.sort (· ≤ ·)).map h with
        | [h] => centered h
        | [h, g] => C (-cumulant [h, g])
        | _ => 1
  have hcast {n n' : ℕ} (hn : n = n') (h : Fin n → FourierProfile) :
      Wick h = Wick (fun i : Fin n' => h (Fin.cast hn.symm i)) := by
    subst n'
    rfl
  rw [← MomentPolynomial.eval_model]
  unfold wickPolynomial
  simp only [MomentPolynomial.eval_sum, List.map_map, Function.comp_def, MomentPolynomial.eval_prod,
    Finset.sum_map_toList, Finset.prod_map_toList, MomentPolynomial.eval_model, wickBlockPolynomial_model]
  change Wick (fun i : Fin L.length => (L.get i).profile) = Wick hs.get
  rw [hcast (List.length_map MomentTest.profile).symm]
  congr 1
  funext i
  simp [hs, List.get_eq_getElem]

private theorem wickBlockPolynomial_bandwidth (L : List MomentTest) :
    ∀ t ∈ wickBlockPolynomial L, MomentWord.bandwidth t.2 ≤ MomentWord.bandwidth L := by
  rcases L with _ | ⟨f, _ | ⟨g, _ | ⟨h, hs⟩⟩⟩
  · simp [wickBlockPolynomial, MomentPolynomial.const, MomentWord.bandwidth]
  · simp [wickBlockPolynomial, MomentPolynomial.atom, MomentPolynomial.const, MomentWord.bandwidth,
      radius_nonneg f.profile_isProfile]
  · simp [wickBlockPolynomial, MomentPolynomial.const, MomentWord.bandwidth]
    exact add_nonneg (radius_nonneg f.profile_isProfile) (radius_nonneg g.profile_isProfile)
  · have hsum : 0 ≤ (hs.map fun f => radius f.profile).sum :=
      List.sum_nonneg (by simpa using fun f (_ : f ∈ hs) => radius_nonneg f.profile_isProfile)
    simp [wickBlockPolynomial, MomentPolynomial.const, MomentWord.bandwidth]
    exact add_nonneg (radius_nonneg f.profile_isProfile)
      (add_nonneg (radius_nonneg g.profile_isProfile) (add_nonneg (radius_nonneg h.profile_isProfile) hsum))

private theorem bandwidth_partition {n : ℕ} (π : Finpartition (Finset.univ : Finset (Fin n)))
    (r : Fin n → ℝ) :
    ∑ B ∈ π.parts, ((B.sort (· ≤ ·)).map r).sum = ∑ i, r i := by
  classical
  have h (B : Finset (Fin n)) : ((B.sort (· ≤ ·)).map r).sum = ∑ i ∈ B, r i := by
    rw [← List.sum_toFinset r (B.sort_nodup (· ≤ ·))]
    simp
  simp_rw [h]
  change ∑ B ∈ π.parts, ∑ i ∈ id B, r i = ∑ i, r i
  rw [← Finset.sum_biUnion π.disjoint, π.biUnion_parts]

/-- Every word in the Wick expansion uses at most the bandwidth of the original list. -/
theorem wickPolynomial_bandwidth (L : List MomentTest) :
    ∀ t ∈ wickPolynomial L, MomentWord.bandwidth t.2 ≤ MomentWord.bandwidth L := by
  classical
  intro t ht
  unfold wickPolynomial MomentPolynomial.sum at ht
  obtain ⟨P, hP, ht⟩ := List.mem_flatten.mp ht
  obtain ⟨π, _, rfl⟩ := List.mem_map.mp hP
  let r := fun i : Fin L.length => radius (L.get i).profile
  have h := MomentPolynomial.bandwidth_prod π.parts.toList
    (fun B => wickBlockPolynomial ((B.sort (· ≤ ·)).map L.get))
    (fun B => MomentWord.bandwidth ((B.sort (· ≤ ·)).map L.get))
    (fun B _ => wickBlockPolynomial_bandwidth ((B.sort (· ≤ ·)).map L.get)) t ht
  simp only [MomentWord.bandwidth, List.map_map, Function.comp_def, Finset.sum_map_toList] at h
  rw [bandwidth_partition π r] at h
  rw [← List.sum_ofFn] at h
  rw [show List.ofFn r = L.map (fun f => radius f.profile) from
    List.ofFn_getElem_eq_map L (fun f => radius f.profile)] at h
  exact h

end Chowla
