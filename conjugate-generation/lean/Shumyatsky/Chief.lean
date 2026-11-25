import Shumyatsky.Coordinates
import Mathlib.GroupTheory.SchurZassenhaus

namespace Shumyatsky
open Subgroup

/-- Standard chief-factor structure in the exact form used by the induction.
The multiple-factor case records the product coordinates and the genuine
G-action on the factors. It makes no generation assumption. -/
inductive ChiefForm {G : Type u} [Group G] (N : Subgroup G) [N.Normal] : Prop
  | elementary (p k : ℕ) (prime : p.Prime) (order : Nat.card N = p^k)
      (abelian : ∀ a b : N, a*b = b*a)
  | single {L : Type u} [Group L] [Finite L] (ρ : G →* L) (onto : Function.Surjective ρ)
      (S : Subgroup L) [S.Normal] [IsSimpleGroup S] (nc : Nonabelian S)
      (image : N.map ρ = S) (inj : Function.Injective (ρ.comp N.subtype))
      (faith : Function.Injective (MulAut.conjNormal (H := S)))
  | multiple {S ι : Type u} [Group S] [Finite S] [IsSimpleGroup S] [Finite ι] [Nontrivial ι]
      (nc : Nonabelian S) (e : N ≃* (ι → S)) (ρ : G →* Labelled ι (MulAut S))
      (trans : ∀ i j, ∃ h : G, (ρ h).perm i = j)
      (restriction : ∀ n : N, ρ n = Labelled.base (fun i => MulAut.conj (e n i)))

variable {G : Type u} [Group G] [Finite G]

def MinimalNormal (N : Subgroup G) : Prop := N ≠ ⊥ ∧
  ∀ K : Subgroup G, K.Normal → K ≤ N → K ≠ ⊥ → K = N

theorem exists_minimal_normal [Nontrivial G] :
    ∃ (N : Subgroup G) (_ : N.Normal), MinimalNormal N := by
  classical
  let good (n : ℕ) := ∃ K : Subgroup G, K.Normal ∧ K ≠ ⊥ ∧ Nat.card K = n
  have hex : ∃ n, good n := ⟨_,⊤,inferInstance,top_ne_bot,rfl⟩
  obtain ⟨N,hN,hne,hn⟩ := Nat.find_spec hex
  refine ⟨N,hN,hne,fun K hK hle hne => eq_of_le_of_card_ge hle ?_⟩
  rw [hn]
  exact Nat.find_min' hex (show good (Nat.card K) from ⟨K,hK,hne,rfl⟩)

theorem abelian_prime_power {N : Subgroup G} [N.Normal] (hm : MinimalNormal N)
    (ab : ∀ a b : N, a*b = b*a) : ∃ p k : ℕ, p.Prime ∧ Nat.card N = p^k := by
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd ((N.one_lt_card_iff_ne_bot.mpr hm.1).ne')
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := N) p hd
  let K : Subgroup G := {
    carrier := {s | s ∈ N ∧ s ^ p = 1}
    one_mem' := ⟨N.one_mem,one_pow _⟩
    mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, by
      have hc : Commute a b := congrArg Subtype.val (ab ⟨a,ha.1⟩ ⟨b,hb.1⟩)
      rw [hc.mul_pow,ha.2,hb.2,one_mul]⟩
    inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow,ha.2,inv_one]⟩ }
  have hk : K.Normal := ⟨fun a ha g => ⟨Subgroup.Normal.conj_mem inferInstance a ha.1 g, by
    change (MulAut.conj g a)^p = 1
    rw [← map_pow,ha.2,map_one]⟩⟩
  have hkn : K ≠ ⊥ := by
    intro h
    have mem : v.val ∈ K := ⟨v.property,congrArg Subtype.val (hv ▸ pow_orderOf_eq_one v : v^p = 1)⟩
    have he : v = 1 := Subtype.ext (h ▸ mem : v.val ∈ (⊥ : Subgroup G))
    exact hp.ne_one (hv ▸ orderOf_eq_one_iff.mpr he)
  have eq := hm.2 K hk (fun _ h => h.1) hkn
  have pg : IsPGroup p N := fun s => ⟨1,by
    have mem : s.val ∈ K := eq.symm ▸ s.property
    apply Subtype.ext
    simpa using mem.2⟩
  obtain ⟨k,h⟩ := pg.exists_card_eq
  exact ⟨p,k,hp,h⟩

theorem elementary_form {N : Subgroup G} [N.Normal] (hm : MinimalNormal N)
    (ab : ∀ a b : N, a*b = b*a) : ChiefForm N := by
  obtain ⟨p,k,hp,h⟩ := abelian_prime_power hm ab
  exact .elementary p k hp h ab

theorem single_form {N : Subgroup G} [N.Normal] [IsSimpleGroup N] (nc : Nonabelian N) :
    ChiefForm N := by
  let c := MulAut.conjNormal (H := N)
  let L := c.range
  let ρ := c.rangeRestrict
  let S := N.map ρ
  have hρ : Function.Surjective ρ := c.rangeRestrict_surjective
  letI : S.Normal := Subgroup.Normal.map inferInstance ρ hρ
  have inner_on (n : N) : c (n : G) = MulAut.conj n := by ext; rfl
  have inj : Function.Injective (ρ.comp N.subtype) := by
    intro a b h
    apply conj_injective_of_simple nc
    simpa only [← inner_on] using congrArg Subtype.val h
  let f := ρ.subgroupMap N
  have bij : Function.Bijective f := ⟨fun _ _ h => inj (congrArg Subtype.val h),ρ.subgroupMap_surjective N⟩
  let e := MulEquiv.ofBijective f bij
  letI : IsSimpleGroup S := e.isSimpleGroup_congr.mp inferInstance
  have faith : Function.Injective (MulAut.conjNormal (H := S)) := by
    apply (MulAut.conjNormal (H := S)).ker_eq_bot_iff.mp
    rw [eq_bot_iff_forall]
    intro l hl
    obtain ⟨g,rfl⟩ := hρ l
    apply Subtype.ext
    ext n
    have hg : MulAut.conjNormal (H := S) (ρ g) = 1 := hl
    have h := DFunLike.congr_fun hg (e n)
    apply congrArg Subtype.val
    apply inj
    change ρ (g*(n : G)*g⁻¹) = ρ n
    simpa only [map_mul,map_inv] using congrArg Subtype.val h
  have nS : Nonabelian S := by
    obtain ⟨a,b,hn⟩ := nc
    exact ⟨e a,e b,fun h => hn (e.injective (by simpa using h))⟩
  exact .single ρ hρ S nS rfl inj faith

omit [Finite G] in
theorem power_form {N : Subgroup G} [N.Normal] (hm : MinimalNormal N)
    {ι S : Type u} [Finite ι] [Nontrivial ι] [Group S] [IsSimpleGroup S] [Finite S]
    (nc : Nonabelian S) (e : N ≃* (ι → S)) : ChiefForm N := by
  classical
  let φ := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))
  let ρ := (Coordinates.action nc).comp φ
  have eqv (g : G) (n : N) (i : ι) :
      e (MulAut.conjNormal g n) ((ρ g).perm i) = (ρ g).label i (e n i) := by
    have h := Coordinates.action_apply nc (φ g) (e n) i
    simpa [φ,MulAut.congr] using h
  have rest (n : N) : ρ n = Labelled.base (fun i => MulAut.conj (e n i)) := by
    change Coordinates.action nc (φ (n : G)) = _
    rw [show φ (n : G) = MulAut.conj (e n) by
      ext v i
      change e (n * e.symm v * n⁻¹) i = _
      simp [MulAut.conj_apply]]
    exact Coordinates.action_conj nc _
  refine .multiple nc e ρ ?_ rest
  intro i
  let orbit (j : ι) := ∃ g : G, (ρ g).perm i = j
  have hself : orbit i := ⟨1,by rw [map_one]; rfl⟩
  let H : Subgroup N := {
    carrier := {n | ∀ j, ¬orbit j → e n j = 1}
    one_mem' := by simp
    mul_mem' := fun {a b} ha hb j hj => by simp [ha j hj,hb j hj]
    inv_mem' := fun {a} ha j hj => by simp [ha j hj] }
  let K := H.map N.subtype
  have normal : K.Normal := by
    constructor
    rintro _ ⟨n,hn,rfl⟩ g
    refine ⟨MulAut.conjNormal g n,?_,rfl⟩
    intro j hj
    let k := (ρ g).perm.symm j
    have hk : ¬orbit k := by
      rintro ⟨t,ht⟩
      exact hj ⟨g*t,by rw [map_mul,Labelled.mul_perm,ht]; exact (ρ g).perm.apply_symm_apply j⟩
    have he := eqv g n k
    rw [show (ρ g).perm k = j from (ρ g).perm.apply_symm_apply j, hn k hk,map_one] at he
    exact he
  obtain ⟨s,hs⟩ := exists_ne (1 : S)
  let single (j : ι) := e.symm (Pi.mulSingle j s)
  have hns (j : ι) : single j ≠ 1 := by
    intro h
    have he := congrArg (fun n : N => e n j) h
    exact hs (by simpa [single] using he)
  have hi : single i ∈ H := by
    intro j hj
    have ne : j ≠ i := fun h => hj (h ▸ hself)
    simp [single,ne]
  have hne : K ≠ ⊥ := by
    intro h
    have mem : (single i : G) ∈ K := ⟨_,hi,rfl⟩
    exact hns i (Subtype.ext (h ▸ mem : (single i : G) ∈ (⊥ : Subgroup G)))
  have hK := hm.2 K normal (fun _ ⟨n,_,hn⟩ => hn ▸ n.property) hne
  intro j
  by_contra h
  obtain ⟨n,hn,he⟩ := hK.ge (single j).property
  have neq : n = single j := Subtype.ext he
  have ht := (show n ∈ H from hn) j h
  exact hs (by simpa [neq,single] using ht)

end Shumyatsky
