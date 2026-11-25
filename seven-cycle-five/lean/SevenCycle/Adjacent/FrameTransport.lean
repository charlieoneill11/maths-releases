import SevenCycle.Blueprint.Definitions
import SevenCycle.Proof.Symmetry

namespace SevenCycle.Adjacent

open Proof Blueprint Blueprint.SearchSpec

/-- The adjacent frame after moving each marked centre to zero. Its marked
bands start at 6 and 0, and its slab occupies heights 6, 0 and 1. -/
def centred : Frame := ⟨fun _ => 1, fun _ => 6⟩

def centresAtZero (m : Frame) (g : Isometry 4) : Prop :=
  act g (fun k => m.base k + 1) = fun _ => 0

private theorem centred_window : ∀ (s : Bool) (t a x : Height),
    (if s then -(a+1) else a+1) + t = 0 →
    let y := (if s then -x else x) + t
    (y = 6 ∨ y = 0 ∨ y = 1) ↔ (x = a ∨ x = a+1 ∨ x = a+1+1) := by decide

private theorem inSlab_centred (x : Tuple 4) (k : Axis) :
    inSlab centred k x ↔ x k = 6 ∨ x k = 0 ∨ x k = 1 := by
  change x k ∈ ({6, (6 : Height) + 1, (6 : Height) + 1 + 1} : Finset _) ↔ _
  have h : (6 : Height)+1 = 0 := by decide
  simp [h]

theorem inUnion_centred {m : Frame} {g : Isometry 4} (hg : ∀ k, m.gap k = 1)
    (hc : centresAtZero m g) (x : Tuple 4) :
    inUnion centred (act g x) ↔ inUnion m x := by
  have atAxis (l : Axis) : inSlab centred l (act g x) ↔ inSlab m (g.1 l) x := by
    rw [inSlab_centred]
    simp only [inSlab, start, hg, Nat.cast_one, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
    exact centred_window _ _ _ _ (congrFun hc l)
  constructor
  · rintro ⟨l, _, hl⟩
    exact ⟨g.1 l, hg _, (atAxis l).mp hl⟩
  · rintro ⟨k, _, hk⟩
    refine ⟨g.1.symm k, rfl, (atAxis _).mpr ?_⟩
    simpa using hk

/-- Exterior points and code cardinalities are preserved when a signed
permutation moves the four marked centres to zero. -/
theorem exterior_centred {m : Frame} {g : Isometry 4} (hg : ∀ k, m.gap k = 1)
    (hc : centresAtZero m g) {D E : Points} (he : SearchSpec.Exterior m D E) :
    SearchSpec.Exterior centred (actOnCode g D) (actOnCode g E) ∧
    ((actOnCode g D) ∪ (actOnCode g E)).card = (D ∪ E).card := by
  have union_eq : actOnCode g D ∪ actOnCode g E = (D ∪ E).image (act g) :=
    (Finset.image_union D E).symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y hy hin
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact he.1 x hx ((inUnion_centred hg hc x).mp hin)
  · rw [union_eq]
    intro x hx y hy h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact he.2 a ha b hb ((Symmetry.act_confusable g a b).mp h)
  · rw [union_eq]
    exact Finset.card_image_of_injective _ (Function.LeftInverse.injective (Symmetry.undo_act g))

end SevenCycle.Adjacent
