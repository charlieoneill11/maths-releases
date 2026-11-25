import Shumyatsky.Reconstruction

namespace Shumyatsky.Block
open Equiv Equiv.Perm

variable {ι A O : Type*} [Finite ι] [Group A] [Group O]
abbrev Edge (ι : Type*) := Sum ι ι
private def src : Edge ι → ι := Sum.elim id id
private def dst (σ τ : Perm ι) : Edge ι → ι := Sum.elim σ τ

/-- A closed labelled walk at the chosen factor. -/
def loops (σ τ : Perm ι) (x y : ι → A) (root : ι) : Subgroup A where
  carrier := {a | Walk σ τ x y (fun _ => True) (fun _ => True) root root a}
  one_mem' := .refl _
  mul_mem' h k := .comp k h
  inv_mem' h := .rev h

/-- The local consequence of the almost-simple generation theorem and Gaschütz. -/
def CanLiftTwo (q : A →* O) : Prop := ∀ u v : A, ∃ a b : A,
  q a = q u ∧ q b = q v ∧ q.ker ≤ Subgroup.closure {a,b}

private theorem select_edges [Nontrivial ι] (σ τ γ : Perm ι)
    (perm : ∀ i, γ (σ i) = τ (γ i)) (trans : Walk.connectedBy σ τ)
    (x y : ι → A) (root : ι) :
    ∃ (keep : Edge ι → Prop) (u v : Edge ι), u ≠ v ∧ ¬keep u ∧ ¬keep v ∧
      (∀ i, keep (.inr (γ i)) ∨ u = .inr (γ i) ∨ v = .inr (γ i) → Cycle.free σ i) ∧
      ∀ i, ∃ a, Walk σ τ x y (fun j => keep (.inl j)) (fun j => keep (.inr j)) root i a := by
  classical
  by_cases h : ∀ i j, σ.SameCycle i j
  · obtain ⟨j, hj⟩ := exists_ne (σ.symm (Cycle.anchor σ root))
    have hfree : Cycle.free σ j := by
      intro e
      apply hj
      apply σ.injective
      rw [σ.apply_symm_apply, ← Cycle.anchor_eq (h j root)]
      exact e
    refine ⟨Sum.elim (· ≠ root) (fun _ => False), .inl root, .inr (γ j),
      by simp, by simp, by simp, ?_, Walk.one_cycle_paths h x y root root⟩
    intro i hi
    have e : j = i := γ.injective (Sum.inr.inj (hi.resolve_left (by simp) |>.resolve_left (by simp)))
    exact e ▸ hfree
  · push_neg at h
    obtain ⟨i,j,hij⟩ := h
    have ne : i ≠ j := fun e => hij (e.sameCycle σ)
    let X k := k ≠ i ∧ k ≠ j
    let Y k := Cycle.free σ (γ.symm k)
    have hx : ∀ a b, ¬X a → ¬X b → σ.SameCycle a b → a = b := by
      intro a b ha hb hab
      simp only [X, not_and_or, not_not] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact (hij hab).elim
      · exact (hij hab.symm).elim
      · rfl
    have hy : ∀ a b, ¬Y a → ¬Y b → τ.SameCycle a b → a = b := by
      intro a b ha hb hab
      apply γ.symm.injective
      apply Cycle.free_unique σ _ _ ha hb
      obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
      have step (k : ι) : γ.symm (τ k) = σ (γ.symm k) := by
        apply γ.injective
        simp [perm]
      clear ha hb hab
      induction n with
      | zero => simp [SameCycle.refl]
      | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, step]; exact ih.apply_right
    refine ⟨Sum.elim X Y, .inl i, .inl j, by simpa, by simp [X], by simp [X], ?_,
      Walk.retained_paths trans x y X Y hx hy root⟩
    intro a ha
    simpa [Y] using ha

/-- The transitive block lemma in source-indexed labels. The new generator and
conjugator have the prescribed outer labels, and the genuine conjugate acts
with a root stabilizer whose restriction contains the entire kernel. -/
theorem lift [Nontrivial ι] (σ τ γ : Perm ι) (perm : ∀ i, γ (σ i) = τ (γ i))
    (trans : Walk.connectedBy σ τ) (q : A →* O) (two : CanLiftTwo q)
    (x₀ y₀ g₀ : ι → A) (base : ∀ i, g₀ (σ i) * x₀ i = y₀ (γ i) * g₀ i) (r : ι) :
    ∃ x y g : ι → A, (∀ i, q (x i) = q (x₀ i)) ∧ (∀ i, q (g i) = q (g₀ i)) ∧
      (∀ i, g (σ i) * x i = y (γ i) * g i) ∧ q.ker ≤ loops σ τ x y r := by
  classical
  let label : Edge ι → A := Sum.elim x₀ y₀
  obtain ⟨keep,u,v,huv,hku,hkv,free,paths⟩ := select_edges σ τ γ perm trans x₀ y₀ r
  choose P hP using paths
  let walkValue (e : Edge ι) := (P (dst σ τ e))⁻¹ * (label e * P (src e))
  obtain ⟨a,b,ha,hb,hab⟩ := two (walkValue u) (walkValue v)
  let assign (e : Edge ι) (w : A) := P (dst σ τ e) * w * (P (src e))⁻¹
  have outer (e : Edge ι) (w : A) (h : q w = q (walkValue e)) :
      q (assign e w) = q (label e) := by simp [assign, h, walkValue, mul_assoc]
  let z e := if e = u then assign u a else if e = v then assign v b else label e
  have hz (e) : q (z e) = q (label e) := by
    by_cases he : e = u
    · subst e; simpa [z] using outer u a ha
    by_cases hf : e = v
    · subst e; simpa [z, he] using outer v b hb
    simp [z, he, hf]
  have fixed (e) (h : keep e) : z e = label e := by
    simp [z, show e ≠ u from fun he => hku (he ▸ h), show e ≠ v from fun he => hkv (he ▸ h)]
  let x i := z (.inl i)
  have eqouter (i : ι) : q (g₀ (σ i)) * q (x i) = q (z (.inr (γ i))) * q (g₀ i) := by
    simpa only [x, hz, label, Sum.elim_inl, Sum.elim_inr, map_mul] using congrArg q (base i)
  obtain ⟨g,yPull,hg,_,hy,eqn⟩ := Cycle.reconstruct σ q x _ g₀ eqouter
  let y i := yPull (γ.symm i)
  have y_eq (i : ι) (h : keep (.inr i) ∨ u = .inr i ∨ v = .inr i) : y i = z (.inr i) := by
    have hi := free (γ.symm i) (by simpa using h)
    simpa [y] using hy _ hi
  have path (i) := Walk.transfer (x' := x) (y' := y)
    (fun j hj => fixed (.inl j) hj)
    (fun j hj => (y_eq j (Or.inl hj)).trans (fixed (.inr j) hj)) (hP i)
  have edge (e : Edge ι) (he : e = u ∨ e = v) :
      Walk σ τ x y (fun _ => True) (fun _ => True) (src e) (dst σ τ e) (z e) := by
    cases e with
    | inl i => exact .first trivial
    | inr i =>
      rw [← y_eq i (Or.inr (he.imp Eq.symm Eq.symm))]
      exact .second trivial
  have loop (e) (he : e = u ∨ e = v) (w : A) (hw : z e = assign e w) :
      w ∈ loops σ τ x y r := by
    have walk := ((path (src e)).comp (edge e he)).comp (path (dst σ τ e)).rev
    simpa [loops, hw, assign, mul_assoc] using walk
  refine ⟨x,y,g,fun i => hz (.inl i),hg,fun i => by simpa [y] using eqn i, hab.trans ?_⟩
  rw [Subgroup.closure_le]
  intro t ht
  rcases Set.mem_insert_iff.mp ht with h | h
  · rw [h]
    exact loop u (Or.inl rfl) a (by simp [z])
  · exact Set.mem_singleton_iff.mp h ▸ loop v (Or.inr rfl) b (by simp [z, huv.symm])

end Shumyatsky.Block
