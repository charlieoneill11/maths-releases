import Shumyatsky.Spectrum
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace Shumyatsky

variable {G ι : Type*} [Group G]
variable (N : ι → Subgroup G) [∀ i, (N i).Normal]
variable (separate : Pairwise fun i j => Disjoint (N i) (N j))

include separate

/-- Conjugation by an element of a different normal direct factor acts trivially. -/
theorem other_block {i j : ι} (h : i ≠ j) (u : N j) :
    MulAut.conjNormal (H := N i) (u : G) = 1 := by
  ext v
  change (u : G) * (v : G) * (u : G)⁻¹ = v
  have hc := Subgroup.commute_of_normal_of_disjoint (N j) (N i) inferInstance inferInstance
    (separate h.symm) u v u.property v.property
  rw [hc.eq, mul_inv_cancel_right]

open scoped Classical in
/-- Multiply the actual block multipliers in any enumeration. After restriction,
only the multiplier on the specified block survives. -/
theorem restrict_product (u : ∀ i, N i) (i : ι) (l : List ι) (hl : l.Nodup) :
    MulAut.conjNormal (H := N i) ((l.map fun j => (u j : G)).prod) =
      if i ∈ l then MulAut.conj (u i) else 1 := by
  classical
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hl
    by_cases e : i = j
    · subst j
      simp [hj, ih hnd]
      ext v
      rfl
    · simp [e, other_block N separate e, ih hnd]

variable [Fintype ι]

/-- Realize all requested actions of one lift, retaining its image in the quotient. -/
theorem realize_lift (M : Subgroup G) [M.Normal] (inside : ∀ i, N i ≤ M)
    (x₀ : G) (a : ∀ i, MulAut (N i))
    (coset : ∀ i, ∃ u : N i, MulAut.conjNormal x₀ * MulAut.conj u = a i) :
    ∃ x : G, QuotientGroup.mk' M x = QuotientGroup.mk' M x₀ ∧
      ∀ i, MulAut.conjNormal x = a i := by
  classical
  choose u hu using coset
  let l : List ι := Finset.univ.toList
  let m : G := (l.map fun j => (u j : G)).prod
  have hm : m ∈ M := by
    apply M.list_prod_mem
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact inside j (u j).property
  refine ⟨x₀ * m, ?_, ?_⟩
  · simpa using hm
  · intro i
    rw [map_mul, show MulAut.conjNormal (H := N i) m = MulAut.conj (u i) by
      simpa [l] using restrict_product N separate u i l Finset.univ.nodup_toList]
    exact hu i

/-- Realize both cosets, including the action of the resulting conjugate. -/
theorem realize_pair (M : Subgroup G) [M.Normal] (inside : ∀ i, N i ≤ M)
    (x₀ g₀ : G) (a b : ∀ i, MulAut (N i))
    (ha : ∀ i, ∃ u : N i, MulAut.conjNormal x₀ * MulAut.conj u = a i)
    (hb : ∀ i, ∃ v : N i, MulAut.conjNormal g₀ * MulAut.conj v = b i) :
    ∃ x g : G, QuotientGroup.mk' M x = QuotientGroup.mk' M x₀ ∧
      QuotientGroup.mk' M g = QuotientGroup.mk' M g₀ ∧ ∀ i,
        MulAut.conjNormal x = a i ∧ MulAut.conjNormal g = b i ∧
        MulAut.conjNormal (g * x * g⁻¹) = b i * a i * (b i)⁻¹ := by
  obtain ⟨x, hx, hxa⟩ := realize_lift N separate M inside x₀ a ha
  obtain ⟨g, hg, hgb⟩ := realize_lift N separate M inside g₀ b hb
  exact ⟨x, g, hx, hg, fun i => ⟨hxa i, hgb i, by simp [hxa i, hgb i]⟩⟩

end Shumyatsky
