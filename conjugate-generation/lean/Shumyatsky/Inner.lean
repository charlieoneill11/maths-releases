import Shumyatsky.FactorAction
import Shumyatsky.Gaschutz
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Center

namespace Shumyatsky
open Subgroup

variable {S : Type*} [Group S]

def Nonabelian (S : Type*) [Group S] : Prop := ∃ a b : S, a*b ≠ b*a

def inner (S : Type*) [Group S] : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range

instance : (inner S).Normal where
  conj_mem h hh g := by
    obtain ⟨s,rfl⟩ := hh
    refine ⟨g s,?_⟩
    ext v
    change g s * v * (g s)⁻¹ = g (s * (g.symm v) * s⁻¹)
    simp

theorem conj_injective_of_simple [IsSimpleGroup S] (hn : Nonabelian S) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  let f := (MulAut.conj : S →* MulAut S)
  apply f.ker_eq_bot_iff.mp
  apply (inferInstance : f.ker.Normal).eq_bot_or_eq_top.resolve_right
  intro h
  obtain ⟨a,b,hab⟩ := hn
  have ha : f a = 1 := show a ∈ f.ker from h ▸ mem_top _
  have he := DFunLike.congr_fun ha b
  exact hab (mul_inv_eq_iff_eq_mul.mp he)

theorem inner_card [IsSimpleGroup S] (hn : Nonabelian S) : Nat.card (inner S) = Nat.card S :=
  (Nat.card_congr (Equiv.ofInjective _ (conj_injective_of_simple hn))).symm

private def tuple {T : Type*} (a b : T) : Bool → T
  | false => a
  | true => b

private theorem tuple_gen {T : Type*} [Group T] (w : Bool → T) :
    Gaschutz.generated w = Subgroup.closure {w false,w true} := by
  unfold Gaschutz.generated
  apply congrArg Subgroup.closure
  change Set.range w = _
  ext t
  constructor
  · rintro ⟨i,rfl⟩
    cases i <;> simp
  · rintro (h | h)
    · exact ⟨false,h.symm⟩
    · exact ⟨true,(Set.mem_singleton_iff.mp h).symm⟩

/-- Gaschütz turns ordinary two-generation of each inverse image into lifts
of the specific ordered outer walk images. -/
theorem liftTwo_of_two_generated {A O : Type*} [Group A] [Group O] [Finite A] [Finite O]
    (q : A →* O) (hq : Function.Surjective q)
    (rankTwo : ∀ u v : A, let L := (Subgroup.closure {q u,q v}).comap q
      ∃ a b : L, Subgroup.closure {a,b} = ⊤) : Block.CanLiftTwo q := by
  classical
  intro u v
  let E := Subgroup.closure {q u,q v}
  let L := E.comap q
  let φ := (q.comp L.subtype).codRestrict E (fun l => l.property)
  have onto : Function.Surjective φ := by
    intro e
    obtain ⟨l,hl⟩ := hq e
    exact ⟨⟨l,show q l ∈ E from hl ▸ e.property⟩,Subtype.ext hl⟩
  let a : E := ⟨q u,subset_closure (by simp)⟩
  let b : E := ⟨q v,subset_closure (by simp)⟩
  have hab : Subgroup.closure {a,b} = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, E.range_subtype]
    rfl
  obtain ⟨s,t,hst⟩ := rankTwo u v
  letI := Fintype.ofFinite L
  obtain ⟨w,hw,hgen⟩ := Gaschutz.lift φ onto (tuple s t) ((tuple_gen _).trans hst)
    (tuple a b) ((tuple_gen _).trans hab)
  have he := congrArg (Subgroup.map L.subtype) ((tuple_gen w).symm.trans hgen)
  rw [MonoidHom.map_closure,Set.image_pair, ← MonoidHom.range_eq_map,L.range_subtype] at he
  refine ⟨w false,w true,congrArg Subtype.val (congrFun hw false),
    congrArg Subtype.val (congrFun hw true),?_⟩
  rw [show Subgroup.closure {((w false : L) : A),((w true : L) : A)} = L from he]
  intro h hh
  change q h ∈ E
  rw [MonoidHom.mem_ker.mp hh]
  exact E.one_mem

end Shumyatsky
