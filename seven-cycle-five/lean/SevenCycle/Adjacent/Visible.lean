import SevenCycleRuntime.FusedMiddle
import SevenCycle.Adjacent.Middle

namespace SevenCycle.Adjacent.ScanFused

open Proof Blueprint Bitsets
open Scan (Marks)

def covered (gaps cs : Marks) (x : Tuple 3) : Bool :=
  (ports gaps cs).any fun (a,j) => Middle.inWindow a j (Middle.Site.ofWord x)

theorem port_start (gaps cs : Marks) (a : Fin 3) (b : Bool) :
    (a, if b then cs.get a else cs.get a - gaps.get a) ∈ ports gaps cs := by
  apply Array.mem_flatMap.mpr
  refine ⟨a, Array.mem_ofFn.mpr ⟨a,rfl⟩, ?_⟩
  cases b <;> simp

theorem covered_at_port {gaps cs : Marks} {a : Fin 3} {j : Contacts.Height}
    (hj : (a,j) ∈ ports gaps cs) {x : Tuple 3} (hx : x a = j ∨ x a = ((show ZMod 7 from j) + (1 : ZMod 7))) :
    covered gaps cs x = true := by
  apply Array.any_eq_true'.mpr
  refine ⟨(a,j),hj,?_⟩
  have eq : Middle.axisValue a (Middle.Site.ofWord x) = x a := by fin_cases a <;> rfl
  have test (z j : Fin 7) : (z == j || z == j+1) = true ↔ (show ZMod 7 from z) = j ∨
      (show ZMod 7 from z) = ((show ZMod 7 from j) + (1 : ZMod 7)) := by
    have h : ∀ z j : Fin 7, (z == j || z == j+1) = true ↔ (show ZMod 7 from z) = j ∨
        (show ZMod 7 from z) = ((show ZMod 7 from j) + (1 : ZMod 7)) := by decide
    exact h _ _
  change (Middle.axisValue a (Middle.Site.ofWord x) == j || Middle.axisValue a (Middle.Site.ofWord x) == (j+1 : Fin 7)) = true
  rw [eq]
  exact (test _ _).mpr hx

/-- All six intersections with marked windows agree for the full middle and
the partial middle whose unmarked sites have been set to zero. -/
theorem visible_cuts {gaps cs : Marks} {u v : Cube}
    (hv : cubeSet v = (cubeSet u).filter (fun x => covered gaps cs x)) {a : Fin 3} {j : Contacts.Height}
    (hj : (a,j) ∈ ports gaps cs) : TypeThree.fastCut v a j = TypeThree.fastCut u a j := by
  rw [TypeThree.fastCut_eq, TypeThree.fastCut_eq]
  apply plane_eq_of_set_eq (canonical_cut v a j) (canonical_cut u a j)
  rw [planeSet_cut, planeSet_cut, hv]
  apply congrArg (Finset.image _)
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨⟨h,_⟩,win⟩ => ⟨h,win⟩, fun ⟨h,win⟩ => ⟨⟨h,covered_at_port hj win⟩,win⟩⟩

theorem visible_level {gaps cs : Marks} {u v : Cube}
    (hv : cubeSet v = (cubeSet u).filter (fun x => covered gaps cs x)) (a : Fin 3) :
    (cubeSet v).filter (fun x => x a = cs.get a) =
    (cubeSet u).filter (fun x => x a = cs.get a) := by
  rw [hv]
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨⟨h,_⟩,he⟩ => ⟨h,he⟩,
    fun ⟨h,he⟩ => ⟨⟨h,covered_at_port (port_start gaps cs a true) (Or.inl he)⟩,he⟩⟩

end SevenCycle.Adjacent.ScanFused
