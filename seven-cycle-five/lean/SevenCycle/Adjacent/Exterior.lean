import SevenCycle.Blueprint.Definitions
import SevenCycle.Proof.Witness

/-!
# Certificates for the exterior of four adjacent slabs

A product of four adjacent pairs contains at most one word of a code. A
certificate covers the admissible exterior sites by such boxes. Box origins
may overlap and may be selected by any method.
-/

namespace SevenCycle.Adjacent.Exterior

open Blueprint Blueprint.SearchSpec Proof

structure Certificate where
  base : Tuple 4
  inside : Array (Tuple 4)
  boxes : Array (Tuple 4)

private def allOffsets : Array (Fin 4 → Fin 4) :=
  (Array.finRange 4).flatMap fun a => (Array.finRange 4).flatMap fun b =>
    (Array.finRange 4).flatMap fun c => (Array.finRange 4).map fun d => ![a,b,c,d]

private theorem mem_offsets (w : Fin 4 → Fin 4) : w ∈ allOffsets := by
  have h (i : Fin 4) : i ∈ Array.finRange 4 := Array.mem_ofFn.mpr ⟨i,rfl⟩
  refine Array.mem_flatMap.mpr ⟨w 0, h _, Array.mem_flatMap.mpr ⟨w 1, h _,
    Array.mem_flatMap.mpr ⟨w 2,h _,Array.mem_map.mpr ⟨w 3,h _,?_⟩⟩⟩⟩
  funext k; fin_cases k <;> rfl

private theorem residue_outside : ∀ t u : Height, u ≠ t → u ≠ t+1 → u ≠ t+1+1 →
    ∃ j : Fin 4, t + 3 + (j.val : Height) = u := by decide

def site (base : Tuple 4) (d : Fin 4 → Fin 4) : Tuple 4 :=
  fun k => base k + 3 + ((d k).val : Height)

private def near (x y : Tuple 4) : Bool :=
  (Array.finRange 4).all fun k => let v := x k - y k; v == 0 || v == 1 || v == -1

private theorem near_sound {x y : Tuple 4} (h : near x y = true) : ∀ k, cycleStep (x k) (y k) := by
  intro k
  have hk := Array.all_eq_true'.mp h k (Array.mem_ofFn.mpr ⟨k, rfl⟩)
  simp only [Bool.or_eq_true_iff, beq_iff_eq] at hk
  rcases hk with (e|e)|e <;> simp [cycleStep, e]

def inBox (q x : Tuple 4) : Bool :=
  (Array.finRange 4).all fun k => x k == q k || x k == q k + 1

theorem box_near {q x y : Tuple 4} (hx : inBox q x = true) (hy : inBox q y = true) :
    ∀ k, cycleStep (x k) (y k) := by
  intro k
  have mem : k ∈ Array.finRange 4 := Array.mem_ofFn.mpr ⟨k,rfl⟩
  have h := Array.all_eq_true'.mp hx k mem
  have g := Array.all_eq_true'.mp hy k mem
  simp only [Bool.or_eq_true_iff, beq_iff_eq] at h g
  rcases h with h|h <;> rcases g with g|g <;> simp [cycleStep, h, g]

def check (c : Certificate) : Bool :=
  c.inside.size + c.boxes.size ≤ 112 && allOffsets.all fun d =>
    let x := site c.base d
    c.inside.any (near x) || c.boxes.any (fun q => inBox q x)

/-- Check one suggested blocker for each exterior site. An index addresses
the inside words first, then the covering boxes. -/
def choiceCheck (c : Certificate) (choice : (Fin 4 → Fin 4) → ℕ) : Bool :=
  c.inside.size + c.boxes.size ≤ 112 && allOffsets.all fun d =>
    let x := site c.base d
    let j := choice d
    if h : j < c.inside.size then near x c.inside[j]
    else (c.boxes[j - c.inside.size]?).any fun q => inBox q x

theorem check_of_choiceCheck (c : Certificate) (choice : (Fin 4 → Fin 4) → ℕ)
    (h : choiceCheck c choice = true) : check c = true := by
  obtain ⟨budget, covered⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨budget, Array.all_eq_true'.mpr ?_⟩
  intro d hd
  have hj := Array.all_eq_true'.mp covered d hd
  dsimp only at hj ⊢
  split at hj
  · rename_i hi
    apply Bool.or_eq_true_iff.mpr
    exact Or.inl (Array.any_eq_true'.mpr ⟨_, Array.getElem_mem hi, hj⟩)
  · generalize he : c.boxes[choice d - c.inside.size]? = o at hj
    cases o with
    | none => contradiction
    | some q =>
      apply Bool.or_eq_true_iff.mpr
      exact Or.inr (Array.any_eq_true'.mpr ⟨q, Array.mem_of_getElem? he, hj⟩)

theorem check_sound (c : Certificate) (ok : check c = true) (m : Frame)
    (hb : m.base = c.base) (hg : ∀ k, m.gap k = 1) (E : Points)
    (he : SearchSpec.Exterior m (rowSet c.inside) E) : (rowSet c.inside ∪ E).card ≤ 112 := by
  classical
  obtain ⟨hbound, hall⟩ := Bool.and_eq_true_iff.mp ok
  have budget : c.inside.size + c.boxes.size ≤ 112 := of_decide_eq_true hbound
  let D := rowSet c.inside
  have cover (x : ↥(E \ D)) : ∃ j : Fin c.boxes.size, inBox c.boxes[j] x.val = true := by
    obtain ⟨hxE, hout⟩ := Finset.mem_sdiff.mp x.property
    have out (k : Axis) : ¬ inSlab m k x.val := fun h => he.1 _ hxE ⟨k,hg k,h⟩
    have coords (k : Axis) : ∃ j : Fin 4, m.base k + 3 + (j.val : Height) = x.val k := by
      have hk := out k
      simp only [inSlab, start, hg, Nat.cast_one, ↓reduceIte, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hk
      exact residue_outside _ _ hk.1 hk.2.1 hk.2.2
    choose d hd using coords
    have ex : site c.base d = x.val := by rw [← hb]; exact funext hd
    have ht := Array.all_eq_true'.mp hall d (mem_offsets d)
    simp only [ex, Bool.or_eq_true_iff, Array.any_eq_true'] at ht
    rcases ht with ⟨z,hz,hnear⟩ | ⟨q,hq,hbox⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hz
      have hzD : c.inside[i] ∈ D := Finset.mem_image.mpr ⟨⟨i,hi⟩, Finset.mem_univ _, rfl⟩
      exact False.elim (he.2 _ (Finset.mem_union_right _ hxE) _ (Finset.mem_union_left _ hzD)
        ⟨fun e => hout (e.symm ▸ hzD), near_sound hnear⟩)
    · obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp hq
      exact ⟨⟨j,hj⟩,hbox⟩
  choose f hf using cover
  have inj : Function.Injective f := by
    intro x y eq
    apply Subtype.ext
    by_contra hne
    have qeq := congrArg (fun j : Fin c.boxes.size => c.boxes[j]) eq
    have h' : inBox c.boxes[f x] y.val = true :=
      (congrArg (fun q => inBox q y.val) qeq).trans (hf y)
    exact he.2 _ (Finset.mem_union_right _ (Finset.mem_sdiff.mp x.property).1)
      _ (Finset.mem_union_right _ (Finset.mem_sdiff.mp y.property).1)
      ⟨hne, box_near (hf x) h'⟩
  have hE := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe, Fintype.card_fin] at hE
  have hD : D.card ≤ c.inside.size := by
    simpa [D, rowSet] using (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin c.inside.size => c.inside[i]))
  change (D ∪ E).card ≤ 112
  rw [← Finset.union_sdiff_self_eq_union]
  exact (Finset.card_union_le _ _).trans ((Nat.add_le_add hD hE).trans budget)

end SevenCycle.Adjacent.Exterior
