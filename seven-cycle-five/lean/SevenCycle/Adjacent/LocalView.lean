import SevenCycle.Adjacent.SlabReconstruction

namespace SevenCycle.Adjacent.CommonFrame

open Blueprint Proof SearchSpec SlabJoin SlabReconstruction

abbrev View (g : Isometry 4) (cs : Centers) (x : Tuple 4) := center cs (act g x)

theorem view_packing {C : Points} (hc : packing cycleStep C) (g : Isometry 4) (cs : Centers) :
    packing cycleStep (C.image (View g cs)) := by
  let tr : Isometry 4 := (Equiv.refl _, fun _ => false,
    fun i => -Fin.cons (α := fun _ => ZMod 7) 1 (fun a => cs.get a) i)
  have move (w : Tuple 4) : center cs w = act tr w := by
    funext i
    simp [center,act,tr,sub_eq_add_neg]
  intro x hx y hy h
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  rw [show View g cs a = act tr (act g a) from move _,show View g cs b = act tr (act g b) from move _] at h
  exact hc _ ha _ hb ((Symmetry.act_confusable g _ _).mp ((Symmetry.act_confusable tr _ _).mp h))

theorem view_injective (g : Isometry 4) (cs : Centers) : Function.Injective (View g cs) := by
  intro x y e
  apply Function.LeftInverse.injective (f := act g) (g := act (Symmetry.undo g)) (Symmetry.undo_act g)
  funext j
  exact sub_left_inj.mp (congrFun e j)

theorem mem_local (cs : Centers) (g : Isometry 4) (C : Points) (w : Tuple 4) :
    w ∈ (normSlab (actOnCode g C)).image (center cs) ↔
      ∃ x ∈ C, inThree 0 (View g cs x) ∧ View g cs x = w := by
  have heights : ∀ t : ZMod 7, (t = 0 ∨ t = 1 ∨ t = 2) ↔
      t-1 = 6 ∨ t-1 = 0 ∨ t-1 = 1 := by decide
  have inside (y : Tuple 4) : y ∈ normSlab (actOnCode g C) ↔ y ∈ actOnCode g C ∧ inThree 0 (center cs y) := by
    simp only [normSlab,level,Finset.mem_union,Finset.mem_filter,inThree,center,Fin.cons_zero]
    rw [← heights]
    tauto
  constructor
  · rintro hh
    obtain ⟨_,h,rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨gmem,hi⟩ := (inside _).mp h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp gmem
    exact ⟨x,hx,hi,rfl⟩
  · rintro ⟨x,hx,hin,rfl⟩
    exact Finset.mem_image.mpr ⟨_,(inside _).mpr ⟨Finset.mem_image.mpr ⟨_,hx,rfl⟩,hin⟩,rfl⟩

theorem identityIndex (j : Fin 4) : j = identityOrder[j] := by fin_cases j <;> rfl

def signCode (f : Fin 4 → Bool) : Fin 16 :=
  Fin.ofNat 16 ((f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat)

theorem sign_bit (f : Fin 4 → Bool) (i : Fin 4) : (signCode f).val.testBit i = f i := by
  have all : ∀ (f : Fin 4 → Bool) (i : Fin 4), (signCode f).val.testBit i = f i := by decide +kernel
  exact all _ _

end SevenCycle.Adjacent.CommonFrame
