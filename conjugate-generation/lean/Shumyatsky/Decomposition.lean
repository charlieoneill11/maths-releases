import Shumyatsky.Chief

namespace Shumyatsky
open Subgroup

private theorem invariant_trivial_or_full {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (minimal : MinimalNormal N) (B : Subgroup N) (normal : (B.map N.subtype).Normal) :
    B = ⊥ ∨ B = ⊤ := by
  have inj := Subgroup.map_injective N.subtype_injective
  by_cases hb : B = ⊥
  · exact Or.inl hb
  · right
    apply inj
    have hne : B.map N.subtype ≠ ⊥ := fun h => hb (inj (h.trans (Subgroup.map_bot _).symm))
    rw [minimal.2 _ normal (Subgroup.map_subtype_le B) hne,← MonoidHom.range_eq_map,N.range_subtype]

private theorem normal_of_invariant {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (B : Subgroup N) (stable : ∀ g : G, B.map (MulAut.conjNormal g).toMonoidHom ≤ B) :
    (B.map N.subtype).Normal := by
  constructor
  rintro _ ⟨b,hb,rfl⟩ g
  exact ⟨MulAut.conjNormal g b,stable g ⟨b,hb,rfl⟩,rfl⟩

private theorem minimal_image {T : Type*} [Group T] {K : Subgroup T} [K.Normal]
    (m : MinimalNormal K) (f : MulAut T) : MinimalNormal (K.map f.toMonoidHom) := by
  have pull (B : Subgroup T) : (B.map f.toMonoidHom).comap f.toMonoidHom = B :=
    comap_map_eq_self_of_injective f.injective _
  have hne : K.map f.toMonoidHom ≠ ⊥ := fun h => m.1 (Subgroup.map_injective f.injective (h.trans (Subgroup.map_bot _).symm))
  refine ⟨hne,?_⟩
  intro B hn hle hb
  have sub : B.comap f.toMonoidHom ≤ K := pull K ▸ comap_mono hle
  have full : (B.comap f.toMonoidHom).map f.toMonoidHom = B :=
    map_comap_eq_self_of_surjective f.surjective B
  have ne : B.comap f.toMonoidHom ≠ ⊥ := fun he => hb (by rw [← full,he,Subgroup.map_bot])
  rw [← full,m.2 _ (hn.comap _) sub ne]

private theorem centerless {T : Type*} [Group T] {B : Subgroup T} [B.Normal]
    (m : MinimalNormal B) (nc : Nonabelian B) : center B = ⊥ := by
  apply (invariant_trivial_or_full m (center B) (normal_of_invariant _ (fun g =>
    characteristic_iff_map_le.mp inferInstance _))).resolve_right
  intro h
  obtain ⟨a,b,ne⟩ := nc
  exact ne (mem_center_iff.mp (show b ∈ center B from h ▸ mem_top _) a)

private theorem factor_simple {T ι : Type*} [Group T] [Fintype ι] [DecidableEq ι]
    (B : ι → Subgroup T) [∀ i, (B i).Normal] (m : ∀ i, MinimalNormal (B i))
    (comm : Pairwise fun i j => ∀ x y : T, x ∈ B i → y ∈ B j → Commute x y)
    (onto : Function.Surjective (Subgroup.noncommPiCoprod comm)) (i : ι) : IsSimpleGroup (B i) := by
  let μ := Subgroup.noncommPiCoprod comm
  letI := (B i).nontrivial_iff_ne_bot.mpr (m i).1
  constructor
  intro U hU
  apply invariant_trivial_or_full (m i) U
  constructor
  rintro _ ⟨u,hu,rfl⟩ z
  obtain ⟨t,rfl⟩ := onto z
  refine ⟨t i * u * (t i)⁻¹,hU.conj_mem _ hu _,?_⟩
  have he : Pi.mulSingle i (t i * u * (t i)⁻¹) = t * Pi.mulSingle i u * t⁻¹ := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  simpa [μ] using congrArg μ he

/-- Distinct conjugates of a minimal normal subgroup of N commute. They
generate N by G-minimality. In the nonabelian case their centers are trivial,
which makes their product direct and each factor simple. -/
theorem chief_form {G : Type u} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hm : MinimalNormal N) : ChiefForm N := by
  classical
  by_cases ab : ∀ a b : N, a*b = b*a
  · exact elementary_form hm ab
  have nc : Nonabelian N := by simpa [Nonabelian] using ab
  letI : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hm.1
  obtain ⟨K,hK,mK⟩ := exists_minimal_normal (G := N)
  letI := hK
  let c := MulAut.conjNormal (H := N)
  let factor (g : G) := K.map (c g).toMonoidHom
  let ι := Set.range factor
  let B (i : ι) : Subgroup N := i.val
  letI : Fintype ι := Fintype.ofFinite _
  let idIndex : ι := ⟨factor 1,1,rfl⟩
  have idK : B idIndex = K := by change K.map (c 1).toMonoidHom = K; rw [map_one]; exact K.map_id
  have same (i : ι) : Nonempty (K ≃* B i) := by
    obtain ⟨g,h⟩ := i.property
    exact ⟨((c g).subgroupMap K).trans (MulEquiv.subgroupCongr h)⟩
  have minB (i : ι) : MinimalNormal (B i) := by
    obtain ⟨g,h⟩ := i.property
    change MinimalNormal i.val
    rw [← h]
    exact minimal_image mK (c g)
  letI normB (i : ι) : (B i).Normal := by
    obtain ⟨g,h⟩ := i.property
    change i.val.Normal
    rw [← h]
    exact hK.map _ (c g).surjective
  have comm : Pairwise fun i j => ∀ x y : N, x ∈ B i → y ∈ B j → Commute x y := by
    intro i j ne
    apply commute_of_normal_of_disjoint _ _ inferInstance inferInstance
    rw [disjoint_iff]
    by_contra h
    have e := (minB i).2 (B i ⊓ B j) inferInstance inf_le_left h
    exact ne (Subtype.ext (e.symm.trans ((minB j).2 _ inferInstance inf_le_right h)))
  let P := iSup B
  have normP := normal_of_invariant P (fun g => by
    rw [show P = iSup B from rfl, Subgroup.map_iSup]
    apply iSup_le
    intro i
    obtain ⟨t,ht⟩ := i.property
    let j : ι := ⟨factor (g*t),g*t,rfl⟩
    apply le_trans _ (le_iSup B j)
    change (B i).map (c g).toMonoidHom ≤ factor (g*t)
    rw [show B i = factor t from ht.symm]
    simp only [factor,Subgroup.map_map,map_mul]
    exact le_rfl)
  have full : P = ⊤ := (invariant_trivial_or_full hm P normP).resolve_left (fun h =>
    mK.1 (bot_unique (by rw [← idK,← h]; exact le_iSup B idIndex)))
  let μ := Subgroup.noncommPiCoprod comm
  have onto : Function.Surjective μ := MonoidHom.range_eq_top.mp
    (Subgroup.noncommPiCoprod_range.trans full)
  have ncK : Nonabelian K := by
    by_contra! h
    have hcomm : ∀ a b : K, a*b=b*a := by simpa [Nonabelian] using h
    apply ab
    intro a b
    obtain ⟨v,rfl⟩ := onto a
    obtain ⟨w,rfl⟩ := onto b
    rw [← map_mul,← map_mul]
    congr 1
    funext i
    let e := (same i).some
    exact e.symm.injective (by simpa using hcomm (e.symm (v i)) (e.symm (w i)))
  have ncB (i : ι) : Nonabelian (B i) := by
    obtain ⟨a,b,h⟩ := ncK
    let e := (same i).some
    exact ⟨e a,e b,fun he => h (e.injective (by simpa using he))⟩
  have indep : iSupIndep B := by
    rw [iSupIndep_def]
    intro i
    have central : (⨆ j, ⨆ (_ : j ≠ i), B j) ≤ centralizer (B i) :=
      iSup_le fun j => iSup_le fun h => fun _ hx => mem_centralizer_iff.mpr
        (fun _ hy => (comm h.symm _ _ hy hx).eq)
    apply Subgroup.disjoint_def.mpr
    intro z hz hz'
    have mem : (⟨z,hz⟩ : B i) ∈ center (B i) :=
      mem_center_iff.mpr (fun b => Subtype.ext (mem_centralizer_iff.mp (central hz') b b.property))
    rw [centerless (minB i) (ncB i)] at mem
    exact congrArg Subtype.val (show (⟨z,hz⟩ : B i) = 1 from mem)
  let prod := MulEquiv.ofBijective μ ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep indep,onto⟩
  let e := prod.symm.trans (MulEquiv.piCongrRight (fun i => (same i).some.symm))
  letI : IsSimpleGroup K := idK ▸ factor_simple B minB comm onto idIndex
  cases subsingleton_or_nontrivial ι with
  | inl h =>
    letI := uniqueOfSubsingleton idIndex
    let iso := e.trans (MulEquiv.piUnique (fun _ : ι => K))
    letI : IsSimpleGroup N := iso.isSimpleGroup
    exact single_form nc
  | inr h => exact power_form hm ncK e

end Shumyatsky
