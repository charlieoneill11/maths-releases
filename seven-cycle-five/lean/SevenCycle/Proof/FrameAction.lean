import SevenCycle.Proof.Crossings

namespace SevenCycle.Proof.FrameAction

open Blueprint Blueprint.SearchSpec

/-- A signed axis reversal swaps the earlier and later two-level windows.
Each gap keeps its positive orientation after that swap. -/
def moved (g : Isometry 4) (m : Frame) : Frame :=
  ⟨fun l => m.gap (g.1 l), fun l =>
    Crossings.startValue (g.2.1 l) (g.2.2 l) (start m (g.1 l) (g.2.1 l))⟩

private theorem reverse_start : ∀ (b : Bool) (t a d : Height), (Crossings.startValue b t
    (if b then a+d else a)) + d = Crossings.startValue b t (if b then a else a+d) := by decide

theorem moved_start (g : Isometry 4) (m : Frame) (l : Axis) (b : Bool) :
    start (moved g m) l b =
      Crossings.startValue (g.2.1 l) (g.2.2 l) (start m (g.1 l) (b ^^ g.2.1 l)) := by
  cases b
  · simp [moved, start]
  · simp only [moved, start, ↓reduceIte, Bool.true_xor]
    rw [reverse_start]
    cases g.2.1 l <;> rfl

private theorem level_eq : ∀ (neg : Bool) (t x c : Height),
    (if neg then -x else x) + t = (if neg then -c else c) + t ↔ x = c := by decide

theorem level_image (g : Isometry 4) (C : Points) (l : Axis) (c : Height) :
    level (actOnCode g C) l ((if g.2.1 l then -c else c) + g.2.2 l) =
      (level C (g.1 l) c).image (act g) := by
  ext y
  constructor
  · intro h
    obtain ⟨hy, he⟩ := Finset.mem_filter.mp h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, (level_eq _ _ _ _).mp he⟩, rfl⟩
  · intro h
    obtain ⟨x, hx,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩, (level_eq _ _ _ _).mpr he⟩

private theorem centre_value : ∀ (b : Bool) (t a : Height),
    Crossings.startValue b t (if b then a else a+1) =
      (if b then -(a+1) else a+1) + t := by decide

theorem moved_centre (g : Isometry 4) (m : Frame) (l : Axis) (hg : m.gap (g.1 l) = 1) :
    start (moved g m) l true = (if g.2.1 l then -(start m (g.1 l) true) else start m (g.1 l) true) + g.2.2 l := by
  rw [moved_start]
  simp only [start, hg, Nat.cast_one, ↓reduceIte, Bool.true_xor]
  have step := centre_value (g.2.1 l) (g.2.2 l) (m.base (g.1 l))
  cases hb : g.2.1 l <;> simpa [hb] using step

theorem marked {m : Frame} {C : Points} (g : Isometry 4) (hm : Marked m C) :
    Marked (moved g m) (actOnCode g C) := by
  have inj : Function.Injective (act g) := Function.LeftInverse.injective (Symmetry.undo_act g)
  have full (l : Axis) (b : Bool) : start (moved g m) l b ∈ fullStarts (actOnCode g C) l := by
    rw [moved_start]
    exact (Crossings.full_transport C g inj l _).mpr (hm.2.1 _ _)
  refine ⟨fun l => hm.1 (g.1 l), full, ?_⟩
  intro l hgap
  have hg : m.gap (g.1 l) = 1 := hgap
  obtain ⟨_,_,lo,hi⟩ := hm.2.2 (g.1 l) hg
  have before : start (moved g m) l true - 1 = start (moved g m) l false := by
    simp [start, hgap]
  refine ⟨before ▸ full l false, full l true, ?_⟩
  rw [moved_centre g m l hg, level_image, Finset.card_image_of_injective _ inj]
  exact ⟨lo,hi⟩

/-- Lemma 11's coordinate equation identifies the target anchor axis, sign
and level translation even for a code with nontrivial symmetry. -/
theorem anchor_fields (g : Isometry 4) (k : Axis) (i : Height)
    (eq : ∀ x : Tuple 4, act g x 0 = x k - i) :
    g.1 0 = k ∧ g.2.1 0 = false ∧ g.2.2 0 = -i := by
  let b := g.2.1 0
  let t := g.2.2 0
  have zero := eq (fun _ => 0)
  have one := eq (fun _ => 1)
  have unit := eq (fun j => if j = k then 1 else 0)
  change (if b then -(0:Height) else 0) + t = 0-i at zero
  change (if b then -(1:Height) else 1) + t = 1-i at one
  have pair : ∀ (b : Bool) (t i : Height), (if b then -0 else 0)+t = 0-i →
      (if b then -1 else 1)+t = 1-i → b = false ∧ t = -i := by decide
  obtain ⟨hb,ht⟩ := pair b t i zero one
  refine ⟨?_, hb, ht⟩
  by_contra n
  change (if b then -(if g.1 0 = k then 1 else 0) else (if g.1 0 = k then 1 else 0))+t =
    (if k=k then 1 else 0)-i at unit
  simp only [hb, Bool.false_eq_true, if_false, if_neg n, zero_add, ht] at unit
  exact (by decide : ∀ i : Height, -i ≠ 1-i) i unit

theorem moved_base_zero (g : Isometry 4) (m : Frame) (k : Axis)
    (eq : ∀ x : Tuple 4, act g x 0 = x k - m.base k) : (moved g m).base 0 = 0 := by
  obtain ⟨ha,hb,ht⟩ := anchor_fields g k (m.base k) eq
  simp [moved, ha, hb, ht, start, Crossings.startValue]

end SevenCycle.Proof.FrameAction
