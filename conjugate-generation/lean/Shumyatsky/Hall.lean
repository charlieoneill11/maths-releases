import Shumyatsky.Chief
import Mathlib.GroupTheory.Solvable

namespace Shumyatsky
open Subgroup

theorem minimal_normal_abelian {G : Type*} [Group G] [IsSolvable G] {N : Subgroup G} [N.Normal]
    (hm : MinimalNormal N) : ∀ a b : N, a*b=b*a := by
  have hlt := IsSolvable.commutator_lt_of_ne_bot hm.1
  have he : ⁅N,N⁆ = ⊥ := by
    by_contra h
    exact hlt.ne (hm.2 _ inferInstance hlt.le h)
  intro a b
  exact Subtype.ext (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he b.property)
    a a.property)

/-- The part of Hall's theorem needed here, proved by induction on a soluble
group. The chosen subgroup captures every prime outside the divisor set of m. -/
theorem soluble_hall_spectrum (m : ℕ) (G : Type u) [Group G] [Finite G] [IsSolvable G] :
    ∃ H : Subgroup G, m.Coprime (Nat.card H) ∧
      ∀ p ∈ spectrum G, ¬p ∣ m → p ∈ spectrum H := by
  suffices aux : ∀ n (T : Type u) [Group T] [Finite T] [IsSolvable T], Nat.card T = n →
      ∃ H : Subgroup T, m.Coprime (Nat.card H) ∧ ∀ p ∈ spectrum T, ¬p ∣ m → p ∈ spectrum H
    from aux _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T _ _ _ hc
    cases subsingleton_or_nontrivial T with
    | inl hs => exact ⟨⊤,by simp,fun _ h _ => (spectrum_eq_of_card_eq Subgroup.card_top).ge h⟩
    | inr ht =>
      obtain ⟨N,hN,hm⟩ := exists_minimal_normal (G := T)
      letI := hN
      obtain ⟨p,k,hp,hpow⟩ := abelian_prime_power hm (minimal_normal_abelian hm)
      have hlt : Nat.card (T ⧸ N) < n := by
        rw [← hc,card_eq_card_quotient_mul_card_subgroup N]
        exact lt_mul_of_one_lt_right Nat.card_pos (N.one_lt_card_iff_ne_bot.mpr hm.1)
      obtain ⟨D,coD,primes⟩ := ih _ hlt (T ⧸ N) rfl
      let f := QuotientGroup.mk' N
      let K := D.comap f
      let φ := (f.comp K.subtype).codRestrict D (fun x => x.property)
      have onto : Function.Surjective φ := by
        intro d
        obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N d
        exact ⟨⟨x,show f x ∈ D from hx ▸ d.property⟩,Subtype.ext hx⟩
      have ker : φ.ker = N.subgroupOf K := by
        ext x
        exact (show φ x = 1 ↔ x.val ∈ N from
          ⟨fun h => (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h),
            fun h => Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)⟩)
      have hsub : N ≤ K := by
        intro x h
        change f x ∈ D
        rw [show f x = 1 from (QuotientGroup.eq_one_iff x).mpr h]
        exact D.one_mem
      have hker : Nat.card φ.ker = Nat.card N := by
        rw [ker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub).toEquiv
      have index : φ.ker.index = Nat.card D := by rw [index_ker,MonoidHom.range_eq_top.mpr onto,card_top]
      have size : Nat.card K = Nat.card N * Nat.card D := by rw [← hker,← index,card_mul_index]
      by_cases hin : p ∣ m
      · have coker : (Nat.card φ.ker).Coprime φ.ker.index := by
          rw [hker,hpow,index]
          exact (coD.coprime_dvd_left hin).pow_left k
        obtain ⟨C,hC⟩ := φ.ker.exists_left_complement'_of_coprime coker
        have hcard : Nat.card (C.map K.subtype) = Nat.card D :=
          (Nat.card_congr (C.equivMapOfInjective _ K.subtype_injective).toEquiv).symm.trans
            (hC.index_eq_card.symm.trans index)
        refine ⟨C.map K.subtype,hcard ▸ coD,?_⟩
        intro s hs hout
        have hd := hs.2
        rw [card_eq_card_quotient_mul_card_subgroup N,hpow] at hd
        have hquot := (hs.1.dvd_mul.mp hd).resolve_right (fun h => hout ((hs.1.dvd_of_dvd_pow h).trans hin))
        exact (spectrum_eq_of_card_eq hcard).ge (primes s ⟨hs.1,hquot⟩ hout)
      · have cok : m.Coprime (Nat.card K) := by
          rw [size,hpow]
          exact Nat.coprime_mul_iff_right.mpr ⟨(hp.coprime_iff_not_dvd.mpr hin).symm.pow_right k,coD⟩
        refine ⟨K,cok,?_⟩
        intro s hs hout
        have hd := hs.2
        rw [card_eq_card_quotient_mul_card_subgroup N] at hd
        rcases hs.1.dvd_mul.mp hd with h | h
        · exact ⟨hs.1,(primes s ⟨hs.1,h⟩ hout).2.trans (Subgroup.card_dvd_of_surjective _ onto)⟩
        · exact ⟨hs.1,h.trans (Subgroup.card_dvd_of_le hsub)⟩

end Shumyatsky
