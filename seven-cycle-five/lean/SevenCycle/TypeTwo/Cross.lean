import SevenCycle.TypeTwo.Coverage
import SevenCycleRuntime.TypeTwoCross

/-! Every genuine sextuple passes all mutually required planar crossings. -/

namespace SevenCycle.TypeTwo.Cross

open Proof Blueprint Blueprint.SearchSpec
open Search (AtlasCovers)

private theorem direction : ∀ a b : Fin 3, a ≠ b → a.succ.succAbove (otherAxis a b) = b.succ := by decide

private theorem order : ∀ a b : Fin 3, a ≠ b → ∀ j : Fin 2,
    a.succ.succAbove ((otherAxis a b).succAbove j) =
    b.succ.succAbove ((otherAxis b a).succAbove j) := by decide

private theorem cross_eq {C : Points} {a b : Slot} (hne : a.1 ≠ b.1) {s t : Cube}
    (hs : TypeThree.RepresentsBand C a.1.succ a.2 s)
    (ht : TypeThree.RepresentsBand C b.1.succ b.2 t) :
    TypeThree.fastCut s (otherAxis a.1 b.1) b.2 = TypeThree.fastCut t (otherAxis b.1 a.1) a.2 := by
  simp only [TypeThree.fastCut_eq]
  exact TypeThree.equal_cuts (direction _ _ hne) (direction _ _ hne.symm) (order _ _ hne) hs ht

private theorem fits_actual {C : Points} (m : Marks) (i j : Fin 6) {s t : Cube}
    (hs : TypeThree.RepresentsBand C m[i].1.succ m[i].2 s)
    (ht : TypeThree.RepresentsBand C m[j].1.succ m[j].2 t) :
    fits m (row m i s) (row m j t) := by
  by_cases h : m[i].1 = m[j].1
  · exact Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr h))
  · apply Bool.or_eq_true_iff.mpr
    right
    apply beq_iff_eq.mpr
    change (Vector.ofFn (fun z : Fin 6 => TypeThree.fastCut s (otherAxis m[i].1 m[z].1) m[z].2))[j.val] =
      (Vector.ofFn (fun z : Fin 6 => TypeThree.fastCut t (otherAxis m[j].1 m[z].1) m[z].2))[i.val]
    simpa only [Vector.getElem_ofFn] using cross_eq (a := m[i]) (b := m[j]) h hs ht

def Covers (C : Points) (m : Marks) (d : Domains) : Prop :=
  ∀ j : Fin 6, ∃ w ∈ d[j], TypeThree.RepresentsBand C m[j].1.succ m[j].2 w

theorem reject_false {C : Points} (m : Marks) (d : Domains) (h : Covers C m d) : reject m d = false := by
  let rows : Vector (Array Row) 6 := Vector.ofFn fun j => d[j].map (row m j)
  let good (b : Row) := ∃ j : Fin 6, ∃ w : Cube, b = row m j w ∧ TypeThree.RepresentsBand C m[j].1.succ m[j].2 w
  have search_ok (n : Nat) (prev : Array Row) (hh : ∀ b ∈ prev, good b) : search m rows n prev := by
    induction n generalizing prev with
    | zero => rfl
    | succ n ih =>
      let i := Fin.ofNat 6 n
      obtain ⟨w,hw,ht⟩ := h i
      let b := row m i w
      have hb : b ∈ rows[i] := by
        change b ∈ rows[i.val]
        simp only [rows, Vector.getElem_ofFn]
        exact Array.mem_map_of_mem (f := row m i) hw
      refine Array.any_eq_true'.mpr ⟨b,hb,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
      · apply Array.all_eq_true_iff_forall_mem.mpr
        intro q hq
        obtain ⟨j,t,rfl,hj⟩ := hh q hq
        exact fits_actual m i j ht hj
      · apply ih
        intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · exact hh q hq
        · exact ⟨i,w,rfl,ht⟩
  simpa [reject,rows] using search_ok 6 #[] (by simp)

end SevenCycle.TypeTwo.Cross
