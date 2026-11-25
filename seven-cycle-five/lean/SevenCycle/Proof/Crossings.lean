import SevenCycle.Blueprint.Definitions
import SevenCycle.Proof.Bands
import SevenCycle.Proof.Symmetry
import Mathlib.Logic.Equiv.Fin.Basic

/-! Crossings of perpendicular bands and reconstruction of adjacent slabs. -/

namespace SevenCycle.Proof.Crossings

open SevenCycle.Blueprint

/-- Project a selection of heights along the given coordinate. -/
private def sectionAt {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1))
    (p : ZMod 7 → Prop) [DecidablePred p] :=
  (C.filter (fun x => p (x k))).image (dropCoord k)

private theorem double_section (C : Finset (Tuple 4)) (k l : Fin 4) (m : Fin 3)
    (h : k.succAbove m = l) (p q : ZMod 7 → Prop) [DecidablePred p] [DecidablePred q] :
    sectionAt (sectionAt C k p) m q =
      (C.filter (fun x => p (x k)) ∩ C.filter (fun x => q (x l))).image
        (fun x => dropCoord m (dropCoord k x)) := by
  ext z
  simp only [sectionAt, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨_, ⟨⟨x, ⟨hx, hp⟩, rfl⟩, hq⟩, rfl⟩
    exact ⟨x, ⟨⟨hx, hp⟩, hx, by simpa only [dropCoord, h] using hq⟩, rfl⟩
  · rintro ⟨x, ⟨⟨hx, hp⟩, _, hq⟩, rfl⟩
    exact ⟨_, ⟨⟨x, ⟨hx, hp⟩, rfl⟩, by simpa only [dropCoord, h] using hq⟩, rfl⟩

private theorem commute_sections (C : Finset (Tuple 4)) (k l : Fin 4) (m m' : Fin 3)
    (hkl : k.succAbove m = l) (hlk : l.succAbove m' = k)
    (p q : ZMod 7 → Prop) [DecidablePred p] [DecidablePred q] :
    sectionAt (sectionAt C k p) m q = sectionAt (sectionAt C l q) m' p := by
  have axes : ∀ (k l : Fin 4) (m m' : Fin 3), k.succAbove m = l → l.succAbove m' = k →
      ∀ j : Fin 2, k.succAbove (m.succAbove j) = l.succAbove (m'.succAbove j) := by decide
  have eq_proj (x : Tuple 4) : dropCoord m (dropCoord k x) = dropCoord m' (dropCoord l x) :=
    funext fun j => congrArg x (axes k l m m' hkl hlk j)
  rw [double_section C k l m hkl, double_section C l k m' hlk, Finset.inter_comm]
  simp only [eq_proj]

theorem crossings (C : Finset (Tuple 4)) (k l : Fin 4) (m m' : Fin 3)
    (hkl : k.succAbove m = l) (hlk : l.succAbove m' = k) (i j : ZMod 7) :
    let W := projectedBand C k i
    let W' := projectedBand C l j
    let proj := fun x : Tuple 4 => dropCoord m (dropCoord k x)
    cut W m j = cut W' m' i ∧
      cut W m j = (band C k i ∩ band C l j).image proj ∧
      ∀ s ∈ ({j, j+1} : Finset (ZMod 7)), lev W m s = (band C k i ∩ level C l s).image proj := by
  let p := fun a : ZMod 7 => a = i ∨ a = i+1
  let q := fun a : ZMod 7 => a = j ∨ a = j+1
  exact ⟨commute_sections C k l m m' hkl hlk p q, double_section C k l m hkl p q,
    fun s _ => double_section C k l m hkl p (· = s)⟩

/-- The two disjoint projected levels partition their band's projection. -/
private theorem band_split {n : ℕ} (C : Finset (Tuple (n+1))) (hC : packing cycleStep C)
    (k : Fin (n+1)) (a : ZMod 7) :
    projectedBand C k a = projectedLevel C k a ∪ projectedLevel C k (a+1) ∧
      Disjoint (projectedLevel C k a) (projectedLevel C k (a+1)) := by
  constructor
  · simp [projectedBand, projectedLevel, band, level, Finset.filter_or, Finset.image_union]
  · apply Finset.disjoint_left.mpr
    intro z hz hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hw
    obtain ⟨hxC, hxa⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyC, hya⟩ := Finset.mem_filter.mp hy
    have hxy := (Bands.band_projection hC k a).1
      (show y ∈ band C k a from Finset.mem_filter.mpr ⟨hyC, Or.inr hya⟩)
      (show x ∈ band C k a from Finset.mem_filter.mpr ⟨hxC, Or.inl hxa⟩) he
    subst y
    have hne : ∀ a : ZMod 7, a ≠ a + 1 := by decide
    exact hne a (hxa.symm.trans hya)

private theorem lift_level {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1)) (t : ZMod 7) :
    level C k t = (projectedLevel C k t).image
      (fun y : Tuple n => k.insertNth (α := fun _ => ZMod 7) t y) := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    exact Fin.insertNth_eq_iff.mpr ⟨(Finset.mem_filter.mp hx).2.symm, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have h : k.insertNth (α := fun _ => ZMod 7) t (dropCoord k y) = y :=
      Fin.insertNth_eq_iff.mpr ⟨(Finset.mem_filter.mp hy).2.symm, rfl⟩
    rwa [h]

private theorem adjacent_levels {n : ℕ} (C : Finset (Tuple (n+1))) (hC : packing cycleStep C)
    (k : Fin (n+1)) (c : ZMod 7) :
    let S := projectedBand C k (c-1)
    let T := projectedBand C k c
    let M := projectedLevel C k c
    M ⊆ S ∩ T ∧ projectedLevel C k (c-1) = S \ M ∧ projectedLevel C k (c+1) = T \ M := by
  dsimp only
  obtain ⟨hS, dS⟩ := band_split C hC k (c-1)
  simp only [sub_add_cancel] at hS dS
  obtain ⟨hT, dT⟩ := band_split C hC k c
  rw [hS, hT]
  exact ⟨Finset.subset_inter Finset.subset_union_right Finset.subset_union_left,
    by ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; grind [Finset.disjoint_left],
    by ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; grind [Finset.disjoint_left]⟩

theorem slabs (C : Finset (Tuple 4)) (hC : packing cycleStep C) (k : Fin 4) (c : ZMod 7) :
    let S := projectedBand C k (c-1)
    let T := projectedBand C k c
    let U := projectedLevel C k c
    let liftAt := fun (t : ZMod 7) (P : Finset (Tuple 3)) =>
      P.image (fun y : Tuple 3 => k.insertNth (α := fun _ => ZMod 7) t y)
    U ⊆ S ∩ T ∧ level C k (c-1) = liftAt (c-1) (S \ U) ∧
      level C k c = liftAt c U ∧ level C k (c+1) = liftAt (c+1) (T \ U) := by
  dsimp only
  obtain ⟨hsub, hlo, hhi⟩ := adjacent_levels C hC k c
  rw [← hlo, ← hhi]
  exact ⟨hsub, lift_level C k _, lift_level C k _, lift_level C k _⟩

theorem slabs_transverse (C : Finset (Tuple 4)) (hC : packing cycleStep C)
    (k l : Fin 4) (m m' : Fin 3) (hkl : k.succAbove m = l) (hlk : l.succAbove m' = k)
    (c t : ZMod 7) (hfull : t ∈ fullStarts C l) :
    let W := projectedBand C l t
    let X := cut (projectedBand C k (c-1)) m t
    let Y := cut (projectedBand C k c) m t
    let M := cut (projectedLevel C k c) m t
    (packing cycleStep W ∧ W.card = 33) ∧ (X, Y, M) = adjacentSignature W m' (c-1) ∧
      lev W m' (c-1) = X \ M ∧ lev W m' c = M ∧ lev W m' (c+1) = Y \ M := by
  dsimp only
  let W := projectedBand C l t
  obtain ⟨hinj, hW⟩ := Bands.band_projection hC l t
  have HW : W.card = 33 := (Finset.card_image_iff.mpr hinj).trans (Finset.mem_filter.mp hfull).2
  have hX := (crossings C k l m m' hkl hlk (c-1) t).1
  have hY := (crossings C k l m m' hkl hlk c t).1
  have hM : cut (projectedLevel C k c) m t = lev W m' c :=
    commute_sections C k l m m' hkl hlk (· = c) (fun a => a = t ∨ a = t+1)
  rw [hX, hY, hM]
  obtain ⟨_, hlo, hhi⟩ := adjacent_levels W hW m' c
  exact ⟨⟨hW, HW⟩, by simp [adjacentSignature, W], hlo, rfl, hhi⟩

/-! ### Transport of full starts, profiles, and atlas representatives -/

/-- A reflection swaps the endpoints of a band, shifting its start by one. -/
def startValue (negate : Bool) (t a : ZMod 7) : ZMod 7 :=
  if negate then -(a+1) + t else a + t

def startEquiv (negate : Bool) (t : ZMod 7) : ZMod 7 ≃ ZMod 7 where
  toFun := startValue negate t
  invFun := if negate then startValue true t else (· - t)
  left_inv := by cases negate <;> intro a <;> simp [startValue, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm]
  right_inv := by cases negate <;> intro a <;> simp [startValue, sub_eq_add_neg,
    add_comm, add_left_comm]

private theorem endpoints : ∀ (negate : Bool) (t a z : ZMod 7),
    let y := (if negate then -z else z) + t
    (y = startValue negate t a ∨ y = startValue negate t a + 1) ↔ (z = a ∨ z = a+1) := by
  decide

private theorem start_distance : ∀ (s : Bool) (t i j : ZMod 7),
    cycleDistance (startValue s t i) (startValue s t j) = cycleDistance i j := by
  decide

/-- Acting on a set then selecting a band is the same as selecting the band first. -/
theorem image_band {n : ℕ} (C : Finset (Tuple (n+1))) (g : Isometry (n+1)) (l : Fin (n+1)) (a : ZMod 7) :
    band (actOnCode g C) l (startValue (g.2.1 l) (g.2.2 l) a) =
      (band C (g.1 l) a).image (act g) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyC, hv⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyC
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,
      (endpoints _ _ _ _).mp hv⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxC, hv⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hxC, rfl⟩,
      (endpoints _ _ _ _).mpr hv⟩

theorem full_transport (C : Finset (Tuple 4)) (g : Isometry 4)
    (inj : Function.Injective (act g)) (l : Fin 4) (a : ZMod 7) :
    startEquiv (g.2.1 l) (g.2.2 l) a ∈ fullStarts (actOnCode g C) l ↔ a ∈ fullStarts C (g.1 l) := by
  simp only [fullStarts, Finset.mem_filter, Finset.mem_univ, true_and]
  change (band _ _ (startValue _ _ _)).card = 33 ↔ _
  rw [image_band, Finset.card_image_of_injective _ inj]

private theorem gap_transport (C : Finset (Tuple 4)) (g : Isometry 4)
    (inj : Function.Injective (act g)) (l : Fin 4) (d : ℕ) :
    AxisGap (actOnCode g C) l d ↔ AxisGap C (g.1 l) d := by
  let e := startEquiv (g.2.1 l) (g.2.2 l)
  have mem (i) := full_transport C g inj l i
  have dist (i j) : cycleDistance (e i) (e j) = cycleDistance i j := start_distance _ _ _ _
  constructor
  · rintro ⟨⟨i, hi, j, hj, hn, hd⟩, hmin⟩
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    refine ⟨⟨i, (mem i).mp hi, j, (mem j).mp hj, fun he => hn (congrArg e he),
      (dist i j).symm.trans hd⟩, ?_⟩
    intro a ha b hb hn
    exact (hmin _ ((mem a).mpr ha) _ ((mem b).mpr hb) (e.injective.ne hn)).trans_eq (dist a b)
  · rintro ⟨⟨i, hi, j, hj, hn, hd⟩, hmin⟩
    refine ⟨⟨e i, (mem i).mpr hi, e j, (mem j).mpr hj, e.injective.ne hn, (dist i j).trans hd⟩, ?_⟩
    intro a ha b hb hn
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    exact (hmin _ ((mem a).mp ha) _ ((mem b).mp hb) (fun h => hn (congrArg e h))).trans_eq
      (dist a b).symm

private theorem multiset_reindex (d : Fin 4 → Fin 3) (σ : Equiv.Perm (Fin 4)) :
    Finset.univ.val.map (fun k => (d (σ k)).val + 1) =
      Finset.univ.val.map (fun k => (d k).val + 1) := by
  change Multiset.map ((fun v : Fin 4 => (d v).val + 1) ∘ σ) _ = _
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem profile_transport (C : Finset (Tuple 4)) (g : Isometry 4) (p : Multiset ℕ) :
    HasProfile C p ↔ HasProfile (actOnCode g C) p := by
  have inj : Function.Injective (act g) := Function.LeftInverse.injective (Symmetry.undo_act g)
  constructor
  · rintro ⟨d, hd, hp⟩
    exact ⟨fun l => d (g.1 l), fun l => (gap_transport C g inj l _).mpr (hd _),
      hp.trans (multiset_reindex d g.1).symm⟩
  · rintro ⟨d, hd, hp⟩
    refine ⟨fun k => d (g.1.symm k), ?_, hp.trans (multiset_reindex d g.1.symm).symm⟩
    intro k
    simpa using (gap_transport C g inj (g.1.symm k) _).mp (hd _)

def liftPerm {n : ℕ} (k : Fin (n+1)) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  ((finSuccEquiv n).trans σ.optionCongr).trans (finSuccEquiv' k).symm

/-- Send axis k to zero and apply the selected three-dimensional isometry on
all other axes, preserving their order in the coordinate deletion. -/
def liftAction {n : ℕ} (k : Fin (n+1)) (i : ZMod 7) (g : Isometry n) : Isometry (n+1) :=
  (liftPerm k g.1, Fin.cons false g.2.1, Fin.cons (-i) g.2.2)

theorem liftAction_spec {n : ℕ} (k : Fin (n+1)) (i : ZMod 7) (g : Isometry n) (x : Tuple (n+1)) :
    act (liftAction k i g) x 0 = x k - i ∧
      dropCoord 0 (act (liftAction k i g) x) = act g (dropCoord k x) := by
  constructor
  · simp [act, liftAction, liftPerm, sub_eq_add_neg]
  · funext j
    simp [act, liftAction, liftPerm, dropCoord]

theorem normalise_full_pair
    (atlas : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 33 →
      ∃ r : Fin atlasPlanes.size, ∃ h : Isometry 3, D = actOnCode h (atlasRepresentative r))
    (C : Finset (Tuple 4)) (hC : packing cycleStep C) (k : Fin 4)
    (i d : ZMod 7) (hi : i ∈ fullStarts C k) (hid : i+d ∈ fullStarts C k) :
    ∃ γ : Isometry 4, ∃ g : Isometry 3,
      (∀ x : Tuple 4, act γ x 0 = x k - i ∧ dropCoord 0 (act γ x) = act g (dropCoord k x)) ∧
      packing cycleStep (actOnCode γ C) ∧
      (∀ p, HasProfile C p ↔ HasProfile (actOnCode γ C) p) ∧
      0 ∈ fullStarts (actOnCode γ C) 0 ∧ d ∈ fullStarts (actOnCode γ C) 0 ∧
      ∃ r : Fin atlasPlanes.size, projectedBand (actOnCode γ C) 0 0 = atlasRepresentative r := by
  let W := projectedBand C k i
  obtain ⟨hinj, hW⟩ := Bands.band_projection hC k i
  have wcard : W.card = 33 := (Finset.card_image_iff.mpr hinj).trans (Finset.mem_filter.mp hi).2
  obtain ⟨r, h, hrow⟩ := atlas W hW wcard
  let g := Symmetry.undo h
  have hgh : Function.LeftInverse (act g) (act h) := Symmetry.undo_act h
  let γ := liftAction k i g
  have hleft : Function.LeftInverse (act (Symmetry.undo γ)) (act γ) := Symmetry.undo_act γ
  have axis : γ.1 0 = k := by simp [γ, liftAction, liftPerm]
  have shift (a : ZMod 7) : startValue (γ.2.1 0) (γ.2.2 0) a = a-i := by
    simp [γ, liftAction, startValue, sub_eq_add_neg]
  have full (a : ZMod 7) : a-i ∈ fullStarts (actOnCode γ C) 0 ↔ a ∈ fullStarts C k := by
    simpa only [startEquiv, Equiv.coe_fn_mk, shift, axis] using full_transport C γ hleft.injective 0 a
  have keeppacking : packing cycleStep (actOnCode γ C) := by
    intro x hx y hy hedge
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hC a ha b hb ((Symmetry.act_confusable γ a b).mp hedge)
  refine ⟨γ, g, liftAction_spec k i g, keeppacking, profile_transport C γ,
    by simpa using (full i).mpr hi, by simpa using (full (i+d)).mpr hid, r, ?_⟩
  have hb := image_band C γ 0 i
  rw [shift, sub_self, axis] at hb
  calc
    projectedBand (actOnCode γ C) 0 0 = actOnCode g W := by
      unfold projectedBand
      rw [hb, Finset.image_image]
      change _ = ((band C k i).image (dropCoord k)).image (act g)
      rw [Finset.image_image]
      exact Finset.image_congr fun x _ => (liftAction_spec k i g x).2
    _ = atlasRepresentative r := by
      rw [hrow]
      unfold actOnCode
      rw [Finset.image_image, hgh.comp_eq_id, Finset.image_id]

end SevenCycle.Proof.Crossings
