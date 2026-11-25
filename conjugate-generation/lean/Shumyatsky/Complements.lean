import Shumyatsky.Abelian

namespace Shumyatsky
open Subgroup

/-- Average the difference of two splittings in an abelian normal Hall
subgroup. This proves the conjugacy part used in the abelian reduction. -/
theorem abelian_hall_conjugacy {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (ab : ∀ a b : N, a*b = b*a) : HallConjugacy N := by
  classical
  letI : CommGroup N := { N.toGroup with mul_comm := ab }
  intro H K co hH hK
  let Q := G ⧸ N
  letI := Fintype.ofFinite Q
  let p := QuotientGroup.mk' N
  let s : Q →* G := H.subtype.comp hH.QuotientMulEquiv.toMonoidHom
  let t : Q →* G := K.subtype.comp hK.QuotientMulEquiv.toMonoidHom
  have ps (i : Q) : p (s i) = i := hH.quotientGroupMk_leftQuotientEquiv i
  have pt (i : Q) : p (t i) = i := hK.quotientGroupMk_leftQuotientEquiv i
  let d (i : Q) : N := ⟨t i * (s i)⁻¹, (QuotientGroup.eq_one_iff _).mp
    (show p (t i * (s i)⁻¹) = 1 by rw [map_mul,map_inv,pt,ps,mul_inv_cancel])⟩
  let act (i : Q) := MulAut.conjNormal (H := N) (s i)
  have cocycle (i j : Q) : d (i*j) = d i * act i (d j) := by
    apply Subtype.ext
    change t (i*j) * (s (i*j))⁻¹ = (t i * (s i)⁻¹) * (s i * (t j * (s j)⁻¹) * (s i)⁻¹)
    simp [mul_assoc]
  let D : N := ∏ j : Q, d j
  have norm (i : Q) : D = d i ^ Fintype.card Q * act i D := calc
    D = ∏ j : Q, d (i*j) := (Equiv.prod_comp (Equiv.mulLeft i) d).symm
    _ = _ := by simp [cocycle,Finset.prod_mul_distrib,D,map_prod]
  have cop : (Nat.card N).Coprime (Fintype.card Q) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr hH.QuotientMulEquiv.toEquiv]
    exact co
  obtain ⟨w,hw⟩ := (powCoprime (G := N) cop).surjective D
  change w ^ Fintype.card Q = D at hw
  have eqd (i : Q) : w = d i * act i w := by
    apply (powCoprime (G := N) cop).injective
    change w ^ Fintype.card Q = (d i * act i w) ^ Fintype.card Q
    rw [mul_pow, ← map_pow, hw, ← norm]
  have conj (i : Q) : (MulAut.conj (w : G)) (s i) = t i := by
    have e := congrArg Subtype.val (eqd i)
    change (w : G) = (t i * (s i)⁻¹) * (s i * w * (s i)⁻¹) at e
    have he : (w : G) * s i = t i * w := by
      simpa [mul_assoc] using congrArg (· * s i) e
    exact mul_inv_eq_iff_eq_mul.mpr he
  refine ⟨w,le_antisymm ?_ ?_⟩
  · intro k hk
    obtain ⟨i,hi⟩ := hK.QuotientMulEquiv.surjective ⟨k,hk⟩
    exact ⟨s i,(hH.QuotientMulEquiv i).property,
      (conj i).trans (congrArg Subtype.val hi)⟩
  · rintro _ ⟨h,hh,rfl⟩
    obtain ⟨i,hi⟩ := hH.QuotientMulEquiv.surjective ⟨h,hh⟩
    have he : s i = h := congrArg Subtype.val hi
    rw [← he]
    exact conj i ▸ (hK.QuotientMulEquiv i).property

end Shumyatsky
