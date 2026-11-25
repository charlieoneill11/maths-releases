import Shumyatsky.Inner
import Mathlib.GroupTheory.NoncommPiCoprod

namespace Shumyatsky.Coordinates
open Subgroup
variable {S ι : Type*} [Group S] [IsSimpleGroup S] [Finite S] [Finite ι] [DecidableEq ι]

private def entry (F : MulAut (ι → S)) (i j : ι) : S →* S :=
  (Pi.evalMonoidHom (fun _ : ι => S) j).comp (F.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : ι => S) i))

omit [Finite ι] in
private theorem bijective_entry {F : MulAut (ι → S)} {i j : ι} (h : entry F i j ≠ 1) :
    Function.Bijective (entry F i j) := by
  have inj := (entry F i j).ker_eq_bot_iff.mp ((inferInstance : (entry F i j).ker.Normal).eq_bot_or_eq_top.resolve_right
    (fun hk => h (MonoidHom.ker_eq_top_iff.mp hk)))
  exact ⟨inj,Finite.surjective_of_injective inj⟩

omit [Finite ι] in
private theorem unique_source (nc : Nonabelian S) {F : MulAut (ι → S)} {i k j : ι}
    (hi : entry F i j ≠ 1) (hk : entry F k j ≠ 1) : i = k := by
  by_contra ne
  obtain ⟨a,b,hn⟩ := nc
  obtain ⟨a',rfl⟩ := (bijective_entry hi).2 a
  obtain ⟨b',rfl⟩ := (bijective_entry hk).2 b
  apply hn
  exact ((Pi.mulSingle_commute (f := fun _ : ι => S) ne a' b').map
    ((Pi.evalMonoidHom (fun _ : ι => S) j).comp F.toMonoidHom)).eq

/-- A labelled permutation represents the action on each coordinate inclusion. -/
def Represents (F : MulAut (ι → S)) (z : Labelled ι (MulAut S)) : Prop :=
  ∀ i s, F (Pi.mulSingle i s) = Pi.mulSingle (z.perm i) (z.label i s)

theorem exists_labels (nc : Nonabelian S) (F : MulAut (ι → S)) : ∃ z, Represents F z := by
  classical
  have exists_dest (i : ι) : ∃ j, entry F i j ≠ 1 := by
    by_contra! h
    obtain ⟨s,hs⟩ := exists_ne (1 : S)
    have he : F (Pi.mulSingle i s) = F 1 := by
      rw [map_one]
      funext j
      exact DFunLike.congr_fun (h j) s
    exact hs (by simpa using F.injective he)
  choose d hd using exists_dest
  have inj : Function.Injective d := fun {i k} e =>
    unique_source nc (hd i) (e.symm ▸ hd k)
  let σ := Equiv.ofBijective d ⟨inj,Finite.surjective_of_injective inj⟩
  let l i := MulEquiv.ofBijective (entry F i (d i)) (bijective_entry (hd i))
  refine ⟨⟨σ,l⟩,?_⟩
  intro i s
  funext j
  by_cases h : j = d i
  · subst j
    change l i s = Pi.mulSingle (M := fun _ : ι => S) (d i) (l i s) (d i)
    simp
  · rw [Pi.mulSingle_eq_of_ne (show j ≠ σ i from h)]
    have he : entry F i j = 1 := by
      by_contra hh
      obtain ⟨k,hk⟩ := σ.surjective j
      have e := unique_source nc hh (show entry F k j ≠ 1 from hk ▸ hd k)
      exact h (hk.symm.trans (congrArg d e.symm))
    exact DFunLike.congr_fun he s

omit [Finite S] [Finite ι] in
theorem labels_unique {F : MulAut (ι → S)} {z w : Labelled ι (MulAut S)}
    (hz : Represents F z) (hw : Represents F w) : z = w := by
  classical
  have eqn (i : ι) (s : S) := (hz i s).symm.trans (hw i s)
  have perm (i : ι) : z.perm i = w.perm i := by
    by_contra ne
    obtain ⟨s,hs⟩ := exists_ne (1 : S)
    have eq := congrFun (eqn i s) (z.perm i)
    simp only [Pi.mulSingle_eq_same,Pi.mulSingle_eq_of_ne ne] at eq
    exact hs ((z.label i).map_eq_one_iff.mp eq)
  apply Labelled.extensionality (Equiv.ext perm)
  intro i
  ext s
  have eq := eqn i s
  rw [perm i] at eq
  exact Pi.mulSingle_injective _ eq

noncomputable def action (nc : Nonabelian S) : MulAut (ι → S) →* Labelled ι (MulAut S) where
  toFun F := (exists_labels nc F).choose
  map_one' := labels_unique (exists_labels nc 1).choose_spec (by intro i s; rfl)
  map_mul' F H := labels_unique (exists_labels nc (F*H)).choose_spec (by
    intro i s
    change F (H (Pi.mulSingle i s)) = _
    rw [(exists_labels nc H).choose_spec,(exists_labels nc F).choose_spec]
    rfl)

theorem action_conj (nc : Nonabelian S) (t : ι → S) :
    action nc (MulAut.conj t) = Labelled.base (fun i => MulAut.conj (t i)) := by
  apply labels_unique (exists_labels nc _).choose_spec
  intro i s
  funext j
  change t j * Pi.mulSingle (M := fun _ : ι => S) i s j * (t j)⁻¹ = Pi.mulSingle (M := fun _ : ι => S) i (t i * s * (t i)⁻¹) j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem action_apply (nc : Nonabelian S) (F : MulAut (ι → S)) (t : ι → S) (i : ι) :
    F t ((action nc F).perm i) = (action nc F).label i (t i) := by
  let z := action nc F
  let ev := Pi.evalMonoidHom (fun _ : ι => S)
  have h : (ev (z.perm i)).comp F.toMonoidHom = (z.label i).toMonoidHom.comp (ev i) := by
    apply MonoidHom.pi_ext
    intro j s
    change F (Pi.mulSingle j s) (z.perm i) = z.label i (Pi.mulSingle (M := fun _ : ι => S) j s i)
    rw [show F (Pi.mulSingle j s) = Pi.mulSingle (z.perm j) (z.label j s) from
      (exists_labels nc F).choose_spec j s]
    by_cases e : i = j
    · subst j; simp
    · simp [e, z.perm.injective.ne e]
  exact DFunLike.congr_fun h t

end Shumyatsky.Coordinates
