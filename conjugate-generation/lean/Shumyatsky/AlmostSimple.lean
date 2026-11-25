import Shumyatsky.Single
import Shumyatsky.Inner
import Shumyatsky.Hall

namespace Shumyatsky
open Subgroup
variable {L : Type*} [Group L]

/-- A simple normal subgroup with faithful conjugation is contained in every
nontrivial normal subgroup. -/
theorem contains_simple (S K : Subgroup L) [S.Normal] [K.Normal] [IsSimpleGroup S]
    (faith : Function.Injective (MulAut.conjNormal (H := S))) (hne : K ≠ ⊥) : S ≤ K := by
  rcases (inferInstance : (K.comap S.subtype).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff_forall]
    intro k hk
    have dis : Disjoint K S := Subgroup.disjoint_def.mpr (fun {s} hs hS => by
      have mem : (⟨s,hS⟩ : S) ∈ K.comap S.subtype := hs
      rw [h] at mem
      exact congrArg Subtype.val (show (⟨s,hS⟩ : S) = 1 from mem))
    apply faith
    rw [map_one]
    ext s
    have hc := Subgroup.commute_of_normal_of_disjoint K S inferInstance inferInstance
      dis k s hk s.property
    change k * (s : L) * k⁻¹ = s
    rw [hc.eq, mul_inv_cancel_right]
  · intro s hs
    exact (show (⟨s,hs⟩ : S) ∈ K.comap S.subtype from h ▸ mem_top _)

/-- The outer quotient of an almost-simple group embeds in the full outer
automorphism group, so Schreier's theorem supplies solubility. -/
theorem outer_solvable (S : Subgroup L) [S.Normal]
    (faith : Function.Injective (MulAut.conjNormal (H := S)))
    [IsSolvable (MulAut S ⧸ inner S)] : IsSolvable (L ⧸ S) := by
  let c := MulAut.conjNormal (H := S)
  let f := (QuotientGroup.mk' (inner S)).comp c
  have own (s : S) : c (s : L) = MulAut.conj s := by ext; rfl
  have ker : f.ker = S := by
    ext l
    change ((c l : MulAut S) : MulAut S ⧸ inner S) = 1 ↔ l ∈ S
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨s,hs⟩
      exact faith ((own s).trans hs) ▸ s.property
    · intro hl
      exact ⟨⟨l,hl⟩,(own ⟨l,hl⟩).symm⟩
  let ψ := QuotientGroup.lift S f ker.ge
  apply solvable_of_solvable_injective (f := ψ)
  apply ψ.ker_eq_bot_iff.mp
  rw [QuotientGroup.ker_lift,ker,QuotientGroup.map_mk'_self]

/-- Every proper quotient factors through the cyclic outer quotient. -/
theorem proper_quotients_cyclic (S : Subgroup L) [S.Normal] [IsSimpleGroup S]
    (faith : Function.Injective (MulAut.conjNormal (H := S))) [IsCyclic (L ⧸ S)]
    (K : Subgroup L) [K.Normal] (hne : K ≠ ⊥) : IsCyclic (L ⧸ K) := by
  let f := QuotientGroup.mk' K
  have h : S ≤ f.ker := by rw [QuotientGroup.ker_mk']; exact contains_simple S K faith hne
  apply isCyclic_of_surjective (QuotientGroup.lift S f h)
  intro y
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective K y
  exact ⟨QuotientGroup.mk' S w,rfl⟩

/-- Turn the Hall subgroup of the outer quotient and the coprime-automorphism
theorem into cyclicity of the quotient, using mathlib's Schur–Zassenhaus. -/
theorem cyclic_outer [Finite L] (hL : Minimal L) (S : Subgroup L) [S.Normal]
    (faith : Function.Injective (MulAut.conjNormal (H := S)))
    (hall : ∃ D : Subgroup (L ⧸ S), (Nat.card S).Coprime (Nat.card D) ∧
      ∀ p ∈ spectrum (L ⧸ S), p ∉ spectrum S → p ∈ spectrum D)
    (coprimeAction : ∀ C : Subgroup (MulAut S), (Nat.card S).Coprime (Nat.card C) → IsCyclic C) :
    IsCyclic (L ⧸ S) := by
  obtain ⟨D,hD,hall⟩ := hall
  have hcop := outer_coprime hL (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
    D (by simpa only [QuotientGroup.ker_mk'] using hD) (by simpa only [QuotientGroup.ker_mk'] using hall)
  rw [QuotientGroup.ker_mk'] at hcop
  obtain ⟨C,hC⟩ := S.exists_left_complement'_of_coprime hcop
  let m := MulAut.conjNormal (H := S)
  let e := C.equivMapOfInjective m faith
  have hcard : Nat.card (L ⧸ S) = Nat.card (C.map m) :=
    (Nat.card_congr hC.QuotientMulEquiv.toEquiv).trans (Nat.card_congr e.toEquiv)
  exact (hC.QuotientMulEquiv.trans e).isCyclic.mpr (coprimeAction _ (hcard ▸ hcop))

end Shumyatsky
