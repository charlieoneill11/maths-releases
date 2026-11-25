import Shumyatsky.Decomposition
import Shumyatsky.Inner
import Shumyatsky.Complements
import Shumyatsky.AlmostSimple

namespace Shumyatsky
open Subgroup

/-- Explicit mathematical inputs to the relative theorem. These four statements are the
classification-dependent inputs used in the proof. -/
structure Inputs.{u} : Prop where
  schreier : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], Nonabelian S →
    IsSolvable (MulAut S ⧸ inner S)
  coprimeAction : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], Nonabelian S →
    ∀ C : Subgroup (MulAut S), (Nat.card S).Coprime (Nat.card C) → IsCyclic C
  conjugateGenerators : ∀ (L : Type u) [Group L] [Finite L], Nonabelian L →
    (∀ (K : Subgroup L) [K.Normal], K ≠ ⊥ → IsCyclic (L ⧸ K)) → ∃ a g : L, pair a g = ⊤
  twoGenerators : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], Nonabelian S →
    let q := QuotientGroup.mk' (inner S)
    ∀ u v : MulAut S, let L := (Subgroup.closure {q u,q v}).comap q
      ∃ a b : L, Subgroup.closure {a,b} = ⊤

/-- Question 17.125, relative to the finite-group inputs recorded above. -/
theorem shumyatsky_of_inputs (facts : Inputs.{u}) (G : Type u) [Group G] [Finite G] :
    ∃ x g : G, spectrum (pair x g) = spectrum G := by
  apply induction_on_normal _ G
  intro T _ _ _ hT
  obtain ⟨N,hN,hmin⟩ := exists_minimal_normal (G := T)
  letI := hN
  have form := chief_form hmin
  refine ⟨N,hN,hmin.1,?_⟩
  intro x g hq
  cases form with
  | elementary p k hp hcard ab =>
    exact abelian_step hT N hmin.1 hp hcard (abelian_hall_conjugacy N ab) x g hq
  | @single L _ _ ρ onto S _ _ nc image inj faith =>
    letI := facts.schreier S nc
    letI := outer_solvable S faith
    obtain ⟨D,co,cover⟩ := soluble_hall_spectrum (Nat.card S) (L ⧸ S)
    have hc := cyclic_outer (minimal_of_surjective hT ρ onto) S faith
      ⟨D,co,fun p hp hout => cover p hp (fun hd => hout ⟨hp.1,hd⟩)⟩ (facts.coprimeAction S nc)
    letI := hc
    letI := IsCyclic.commGroup (α := L ⧸ S)
    have ncL : Nonabelian L := by
      obtain ⟨a,b,hn⟩ := nc
      exact ⟨a,b,fun he => hn (Subtype.ext he)⟩
    have gen := facts.conjugateGenerators L ncL (fun K _ => proper_quotients_cyclic S faith K)
    exact single_step hT N ρ onto (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
      (by rwa [QuotientGroup.ker_mk']) inj gen x g hq
  | @multiple S ι _ _ _ _ _ nc e ρ trans rest =>
    let q := QuotientGroup.mk' (inner S)
    have qker : q.ker = inner S := QuotientGroup.ker_mk' _
    letI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
      DFunLike.coe_injective
    apply block_step N ρ q hT x g hq trans (fun n => by rw [rest]; rfl) _
      (liftTwo_of_two_generated q (QuotientGroup.mk'_surjective _) (facts.twoGenerators S nc))
    · rintro p ⟨hp,hd⟩
      rw [Nat.card_congr e.toEquiv,Nat.card_fun] at hd
      exact ⟨hp, by rw [qker,inner_card nc]; exact hp.dvd_of_dvd_pow hd⟩
    · intro b
      have member (i : ι) : (b i : MulAut S) ∈ inner S := qker.le (b i).property
      choose t ht using member
      refine ⟨e.symm t,?_⟩
      rw [rest,e.apply_symm_apply]
      exact congrArg Labelled.base (funext ht)

/-- The soluble case, with no historical hypotheses. -/
theorem shumyatsky_solvable (G : Type u) [Group G] [Finite G] [IsSolvable G] :
    ∃ x g : G, spectrum (pair x g) = spectrum G := by
  refine induction_on_normal_in (fun T _ => IsSolvable T)
    (fun T _ H _ => inferInstance) (fun T _ N _ _ => inferInstance) ?_ G inferInstance
  intro T _ _ _ _ hm
  obtain ⟨N,hN,hmin⟩ := exists_minimal_normal (G := T)
  letI := hN
  have ab := minimal_normal_abelian hmin
  obtain ⟨p,k,hp,order⟩ := abelian_prime_power hmin ab
  exact ⟨N,hN,hmin.1,abelian_step hm N hmin.1 hp order (abelian_hall_conjugacy N ab)⟩

end Shumyatsky
