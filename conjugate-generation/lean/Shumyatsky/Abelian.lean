import Shumyatsky.Induction
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.OrderOfElement

namespace Shumyatsky
open Subgroup
variable {G : Type*} [Group G]

private theorem first_mem (x g : G) : x ∈ pair x g := subset_closure (by simp)
private theorem second_mem (x g : G) : g*x*g⁻¹ ∈ pair x g := subset_closure (by simp)

private theorem full_of_prime (hG : Minimal G) (N : Subgroup G) [N.Normal]
    (p k : ℕ) (hN : Nat.card N = p^k) (H : Subgroup G)
    (onto : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype)) (h : p ∣ Nat.card H) :
    H = ⊤ := by
  apply finish_normal hG N H onto
  rintro s ⟨hs,hd⟩
  rw [hN] at hd
  exact ⟨hs,(hs.dvd_of_dvd_pow hd).trans h⟩

private theorem complement_of_proper (hG : Minimal G) (N : Subgroup G) [N.Normal]
    {p k : ℕ} (hp : p.Prime) (hN : Nat.card N = p^k) (H : Subgroup G) (proper : H ≠ ⊤)
    (onto : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype)) :
    (Nat.card N).Coprime (Nat.card H) ∧ H.IsComplement' N := by
  have h := hp.coprime_iff_not_dvd.mpr (fun hd => proper (full_of_prime hG N p k hN H onto hd))
  have co : (Nat.card N).Coprime (Nat.card H) := hN ▸ h.pow_left k
  refine ⟨co, isComplement_subgroup_right_iff_bijective.mpr ⟨?_,onto⟩⟩
  intro a b hab
  have hd : Disjoint H N := disjoint_iff.mpr (inf_eq_bot_of_coprime co.symm)
  have hn : a.val⁻¹ * b.val ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N _ = 1
    rw [map_mul,map_inv,show QuotientGroup.mk' N a.val = QuotientGroup.mk' N b.val from hab,
      inv_mul_cancel]
  exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hd
    (H.mul_mem (H.inv_mem a.property) b.property) hn))

/-- The Schur–Zassenhaus conjugacy input for a solvable normal Hall subgroup.
It is passed explicitly so the dependency can be audited. -/
def HallConjugacy (N : Subgroup G) : Prop := ∀ H K : Subgroup G,
  (Nat.card N).Coprime (Nat.card H) → H.IsComplement' N → K.IsComplement' N →
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom

theorem abelian_step [Finite G] (hG : Minimal G) (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    {p k : ℕ} (hp : p.Prime) (hN : Nat.card N = p^k) (schur : HallConjugacy N)
    (x g : G) (quot : pair (QuotientGroup.mk' N x) (QuotientGroup.mk' N g) = ⊤) :
    ∃ a b : G, pair a b = ⊤ := by
  classical
  let H := pair x g
  let f := QuotientGroup.mk' N
  by_cases doneH : H = ⊤
  · exact ⟨x,g,doneH⟩
  obtain ⟨co,comp⟩ := complement_of_proper hG N hp hN H doneH (quotient_pair_surj N _ _ quot)
  have inj := (isComplement_subgroup_right_iff_bijective.mp comp).1
  have uniqueH {a b : G} (ha : a ∈ H) (hb : b ∈ H) (he : f a = f b) : a = b :=
    congrArg Subtype.val (inj (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) he)
  by_cases fixed : ∃ v : N, (v : G) ≠ 1 ∧ Commute x (v : G)
  · obtain ⟨v,hv,hc⟩ := fixed
    have hvp : p ∣ orderOf (v : G) := by
      obtain ⟨l, _, hl⟩ := (Nat.dvd_prime_pow hp).mp (hN ▸ N.orderOf_dvd_natCard v.property)
      cases l with
      | zero => exact (hv (orderOf_eq_one_iff.mp (by simpa using hl))).elim
      | succ l => rw [hl,pow_succ]; exact dvd_mul_left _ _
    have cod := co.symm.coprime_dvd_left (H.orderOf_dvd_natCard (first_mem x g))
    have hord := hc.orderOf_mul_eq_mul_orderOf_of_coprime (cod.coprime_dvd_right (N.orderOf_dvd_natCard v.property))
    have hq : pair (f (x*v)) (f g) = ⊤ := by simpa [f, v.property] using quot
    exact ⟨x*v,g,full_of_prime hG N p k hN _ (quotient_pair_surj N _ _ hq)
      ((hvp.trans (hord ▸ dvd_mul_left _ _)).trans ((pair (x*v) g).orderOf_dvd_natCard (first_mem _ _)))⟩
  · have free (n : N) (e : (MulAut.conj (n : G)) x = x) : (n : G) = 1 := by
      by_contra hn
      apply fixed ⟨n,hn,?_⟩
      exact ((mul_inv_eq_iff_eq_mul.mp e).symm : x * n = n * x)
    obtain ⟨v,hv,hv1⟩ := N.bot_or_exists_ne_one.resolve_left hne
    let n := g*v*g⁻¹
    have hn : n ∈ N := Subgroup.Normal.conj_mem inferInstance v hv g
    have fn : f n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    let y := g*x*g⁻¹
    have moved : n*y*n⁻¹ ∉ H := by
      intro h
      have he := uniqueH h (second_mem x g) (by simp only [y,map_mul,map_inv,fn,one_mul,inv_one,mul_one])
      have e : (MulAut.conj v) x = x := by
        apply (MulAut.conj g).injective
        simpa [n,y,MulAut.conj_apply,mul_assoc] using he
      exact hv1 (free ⟨v,hv⟩ e)
    let K := pair x (n*g)
    refine ⟨x,n*g,?_⟩
    by_contra hk
    have hq : pair (f x) (f (n*g)) = ⊤ := by simpa only [map_mul,fn,one_mul] using (show pair (f x) (f g) = ⊤ from quot)
    obtain ⟨_,ck⟩ := complement_of_proper hG N hp hN K hk (quotient_pair_surj N _ _ hq)
    obtain ⟨m,hm⟩ := schur H K co comp ck
    obtain ⟨t,ht,he⟩ := (hm ▸ first_mem x (n*g) : x ∈ H.map (MulAut.conj (m : G)).toMonoidHom)
    have ht' : t = x := uniqueH ht (first_mem _ _) (by
      have := congrArg f he
      have fm : f (m : G) = 1 := (QuotientGroup.eq_one_iff _).mpr m.property
      change f ((m : G)*t*(m : G)⁻¹) = f x at this
      simpa only [map_mul,map_inv,fm,one_mul,inv_one,mul_one] using this)
    subst t
    have hm1 := free m he
    have hKH : K = H := by
      rw [hm,hm1,map_one]
      exact H.map_id
    apply moved
    have h := second_mem x (n*g)
    change (n*g)*x*(n*g)⁻¹ ∈ K at h
    rw [hKH] at h
    simpa [y,mul_assoc] using h

end Shumyatsky
