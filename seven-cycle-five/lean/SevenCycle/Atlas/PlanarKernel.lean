import SevenCycle.Atlas.Planar
import SevenCycle.Atlas.SmallBounds
import SevenCycle.Proof.Deficits
import SevenCycle.Proof.Crossings
import Mathlib.Tactic.FinCases

/-! Kernel-only classification after normalizing the unique deficient planar band. -/

namespace SevenCycle.Atlas.Planar.Kernel

open SevenCycle.Proof SevenCycle.Blueprint

/-- Above or below a singleton at a, two mutually separated points must occupy
one of the three nonconsecutive pairs among a+2,a+3,a+4,a+5. -/
private def fstOffset : Fin 3 → ZMod 7 := ![2, 2, 3]
private def sndOffset : Fin 3 → ZMod 7 := ![4, 5, 5]
private def pair (a : ZMod 7) (p : Fin 3) : Finset (ZMod 7) :=
  {a + fstOffset p, a + sndOffset p}

private def pattern (a b c : ZMod 7) (p q r : Fin 3) : Finset (Tuple 2) :=
  Finset.univ.filter fun x =>
    x 1 ∈ (![ {0}, {a}, pair a p, {b}, pair b q, {c}, pair 0 r] : ZMod 7 → Finset (ZMod 7)) (x 0)

private def feasible (a b c : ZMod 7) (p q r : Fin 3) : Prop :=
  ¬cycleStep 0 a ∧
  ¬cycleStep (a+fstOffset p) b ∧ ¬cycleStep (a+sndOffset p) b ∧
  ¬cycleStep (b+fstOffset q) c ∧ ¬cycleStep (b+sndOffset q) c ∧
  ¬cycleStep c (fstOffset r) ∧ ¬cycleStep c (sndOffset r)

private instance (a b c : ZMod 7) (p q r : Fin 3) : Decidable (feasible a b c p q r) := by
  unfold feasible cycleStep
  infer_instance

private def address (a b c : ZMod 7) (p q r : Fin 3) : Nat :=
  (((((a.val*7+b.val)*7+c.val)*3+p.val)*3+q.val)*3+r.val)

/-- Candidate row and isometry. The equality checked below validates every
lookup at an admissible pattern, including the default. -/
private def hint : Nat → Fin 3 × Fin 392
  | 2835 => (2, 374)
  | 2836 => (2, 379)
  | 2837 => (0, 363)
  | 2864 => (0, 382)
  | 2867 => (1, 363)
  | 2870 => (0, 144)
  | 3053 => (0, 165)
  | 3062 => (2, 149)
  | 3071 => (2, 152)
  | 4376 => (1, 360)
  | 6423 => (1, 372)
  | 7728 => (2, 132)
  | 7737 => (2, 137)
  | 7746 => (0, 121)
  | 7773 => (0, 375)
  | 7774 => (2, 359)
  | 7775 => (2, 362)
  | 7929 => (0, 140)
  | 7932 => (1, 375)
  | 7935 => (0, 354)
  | _ => (0, 0)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem patterns_checked (a : ZMod 7) :
    ∀ (b c : ZMod 7) (p q r : Fin 3), feasible a b c p q r →
      let t := hint (address a b c p q r)
      pattern a b c p q r = actOnCode (motion t.2) (twoRepresentatives t.1) := by
  fin_cases a <;> decide +kernel


private theorem tuple_two (x : Tuple 2) : ![x 0, x 1] = x := by
  funext j
  fin_cases j <;> rfl

private def row (C : Finset (Tuple 2)) (i : ZMod 7) : Finset (ZMod 7) :=
  Finset.univ.filter fun b => ![i,b] ∈ C

@[simp] private theorem mem_row (C : Finset (Tuple 2)) (i b : ZMod 7) :
    b ∈ row C i ↔ ![i,b] ∈ C := by simp [row]

private theorem row_card (C : Finset (Tuple 2)) (i : ZMod 7) :
    (row C i).card = (level C 0 i).card := by
  refine Finset.card_bij' (fun b _ => ![i,b]) (fun x _ => x 1) ?_ ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_filter.mpr ⟨(mem_row ..).mp hb, rfl⟩
  · intro x hx
    have h := (Finset.mem_filter.mp hx).2
    change x 1 ∈ row C i
    rw [mem_row, ← h, tuple_two]
    exact (Finset.mem_filter.mp hx).1
  · intros; rfl
  · intro x hx
    change ![i, x 1] = x
    rw [← (Finset.mem_filter.mp hx).2]
    exact tuple_two x

private theorem line_bound (R : Finset (Tuple 1)) (hr : packing cycleStep R) : R.card ≤ 3 :=
  Bands.band_bound (a := 1) (fun D _ => D.card_le_univ.trans_eq (by decide)) R hr

private def counts : ZMod 7 → Nat := ![1,1,2,1,2,1,2]

private theorem row_counts {C : Finset (Tuple 2)} (hc : packing cycleStep C) (hs : C.card = 10)
    (hb : (band C 0 0).card ≤ 2) : ∀ i, (row C i).card = counts i := by
  let n := fun i => (level C 0 i).card
  have sum := Bands.sum_level_card C 0
  change ∑ i : ZMod 7, n i = C.card at sum
  rw [hs, Deficits.sum_seven_at _ 0] at sum
  simp only [zero_add] at sum
  have bound (i : ZMod 7) : n i + n (i+1) ≤ 3 := (Bands.band_card C 0 i).symm ▸
    Bands.band_card_le line_bound C hc 0 i
  rw [show (band C 0 0).card = n 0 + n (0+1) from Bands.band_card C 0 0, zero_add] at hb
  have h1 := bound 1
  have h2 := bound 2
  have h3 := bound 3
  have h4 := bound 4
  have h5 := bound 5
  have h6 := bound 6
  change n 1 + n 2 ≤ 3 at h1
  change n 2 + n 3 ≤ 3 at h2
  change n 3 + n 4 ≤ 3 at h3
  change n 4 + n 5 ≤ 3 at h4
  change n 5 + n 6 ≤ 3 at h5
  change n 6 + n 0 ≤ 3 at h6
  intro i
  rw [row_card]
  change n i = counts i
  fin_cases i
  · change n 0 = 1; omega
  · change n 1 = 1; omega
  · change n 2 = 2; omega
  · change n 3 = 1; omega
  · change n 4 = 2; omega
  · change n 5 = 1; omega
  · change n 6 = 2; omega


private def translation (s t : ZMod 7) : Isometry 2 :=
  (Equiv.refl _, fun _ => false, ![s,t])

private theorem translation_apply (s t : ZMod 7) (x : Tuple 2) :
    act (translation s t) x = ![x 0+s, x 1+t] := by
  funext j
  fin_cases j <;> rfl

private theorem missing_band {C : Finset (Tuple 2)} (hs : C.card = 10) :
    ∃ i : ZMod 7, (band C 0 i).card ≤ 2 := by
  by_contra! h
  have big : (∑ _ : ZMod 7, 3) ≤ ∑ i : ZMod 7, (band C 0 i).card :=
    Finset.sum_le_sum (fun i _ => h i)
  rw [show (∑ i : ZMod 7, (band C 0 i).card) = 2*C.card from Bands.sum_band_card C 0] at big
  simp [ZMod.card, hs] at big

private theorem move_code {C : Finset (Tuple 2)} (hc : packing cycleStep C) (g : Isometry 2) :
    packing cycleStep (actOnCode g C) := by
  intro x hx y hy edge
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  exact hc a ha b hb ((Symmetry.act_confusable g a b).mp edge)

private theorem move_card (C : Finset (Tuple 2)) (g : Isometry 2) :
    (actOnCode g C).card = C.card :=
  Finset.card_image_of_injective _ (Function.LeftInverse.injective (Symmetry.undo_act g))

private theorem shift_band (C : Finset (Tuple 2)) (s t : ZMod 7) :
    (band (actOnCode (translation (-s) (-t)) C) 0 0).card = (band C 0 s).card := by
  let g := translation (-s) (-t)
  have he : Crossings.startValue (g.2.1 0) (g.2.2 0) s = 0 := by
    simp [g, translation, Crossings.startValue]
  have hb := Crossings.image_band C g 0 s
  rw [he] at hb
  exact (congrArg Finset.card hb).trans
    (Finset.card_image_of_injective _ (Function.LeftInverse.injective (Symmetry.undo_act g)))

private theorem normalize {C : Finset (Tuple 2)} (hc : packing cycleStep C) (hs : C.card = 10) :
    ∃ s t : ZMod 7, let D := actOnCode (translation (-s) (-t)) C
      packing cycleStep D ∧ (∀ i, (row D i).card = counts i) ∧ (0 : ZMod 7) ∈ row D 0 := by
  obtain ⟨s, hbad⟩ := missing_band hs
  let E := actOnCode (translation (-s) (-0)) C
  have sizes := row_counts (move_code hc _) ((move_card C _).trans hs)
    ((shift_band C s 0).le.trans hbad)
  have he : (row E 0).card = 1 := sizes 0
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (he ▸ Nat.zero_lt_one)
  obtain ⟨x, hx, hxt⟩ := Finset.mem_image.mp ((mem_row ..).mp ht)
  change act (translation (-s) (-0)) x = ![0,t] at hxt
  rw [translation_apply] at hxt
  have hx0 : x 0 + (-s) = 0 := congrFun hxt 0
  have hx1 : x 1 = t := by simpa using congrFun hxt 1
  let g := translation (-s) (-t)
  exact ⟨s, t, move_code hc g, row_counts (move_code hc g) ((move_card C g).trans hs)
    ((shift_band C s t).le.trans hbad), (mem_row ..).mpr (Finset.mem_image.mpr
      ⟨x, hx, by simp [translation_apply, hx0, hx1]⟩)⟩

/-- Word independence forbids a vertical cycle step whenever two row/column pairs
are different words and their heights are equal or adjacent. -/
private theorem row_apart {C : Finset (Tuple 2)} (hc : packing cycleStep C)
    {i j x y : ZMod 7} (hi : cycleStep i j) (hne : i ≠ j ∨ x ≠ y)
    (hx : x ∈ row C i) (hy : y ∈ row C j) : ¬cycleStep x y := by
  intro h
  refine hc _ ((mem_row ..).mp hx) _ ((mem_row ..).mp hy) ⟨?_, ?_⟩
  · intro eq
    rcases hne with hne | hne
    · exact hne (congrFun eq 0)
    · exact hne (congrFun eq 1)
  · intro u
    fin_cases u
    · exact hi
    · exact h

private theorem pairs_possible : ∀ (a : ZMod 7) (B : Finset (ZMod 7)), B.card = 2 →
    (∀ b ∈ B, ¬cycleStep a b) → (∀ b ∈ B, ∀ c ∈ B, b ≠ c → ¬cycleStep b c) →
      ∃ p : Fin 3, B = pair a p := by
  unfold cycleStep
  decide +kernel

private theorem normalize_double {C : Finset (Tuple 2)} (hc : packing cycleStep C)
    {i j a : ZMod 7} (hi : cycleStep i j) (hne : i ≠ j) (ha : a ∈ row C i)
    (hsize : (row C j).card = 2) : ∃ p, row C j = pair a p :=
  pairs_possible _ _ hsize
    (fun _ hb => row_apart hc hi (.inl hne) ha hb)
    (fun _ hb _ hc' hn => row_apart hc (by simp [cycleStep]) (.inr hn) hb hc')

private theorem pattern_rows (a b c : ZMod 7) (p q r : Fin 3) :
    ∀ i, row (pattern a b c p q r) i =
      (![ {0}, {a}, pair a p, {b}, pair b q, {c}, pair 0 r] : ZMod 7 → Finset (ZMod 7)) i := by
  intro i
  ext v
  simp [row, pattern]

private theorem classify_normalized {D : Finset (Tuple 2)} (hc : packing cycleStep D)
    (sizes : ∀ i, (row D i).card = counts i) (origin : (0 : ZMod 7) ∈ row D 0) :
    ∃ t : Fin 3 × Fin 392, D = actOnCode (motion t.2) (twoRepresentatives t.1) := by
  have row0 : row D 0 = {0} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨origin, fun x hx => Finset.card_le_one.mp (show (row D 0).card ≤ 1 by rw [sizes]; decide) x hx 0 origin⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show (row D 1).card = 1 from sizes 1)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (show (row D 3).card = 1 from sizes 3)
  obtain ⟨c, hc'⟩ := Finset.card_eq_one.mp (show (row D 5).card = 1 from sizes 5)
  have ha' : a ∈ row D 1 := ha ▸ Finset.mem_singleton_self _
  have hb' : b ∈ row D 3 := hb ▸ Finset.mem_singleton_self _
  have hc'' : c ∈ row D 5 := hc' ▸ Finset.mem_singleton_self _
  obtain ⟨p, hp⟩ := normalize_double hc (i := 1) (j := 2) (by unfold cycleStep; decide) (by decide)
    ha' (sizes 2)
  obtain ⟨q, hq⟩ := normalize_double hc (i := 3) (j := 4) (by unfold cycleStep; decide) (by decide)
    hb' (sizes 4)
  obtain ⟨r, hr⟩ := normalize_double hc (i := 0) (j := 6) (by unfold cycleStep; decide) (by decide)
    origin (sizes 6)
  have eq : D = pattern a b c p q r := by
    have rows_eq (i : ZMod 7) : row D i = row (pattern a b c p q r) i := by
      rw [pattern_rows]
      fin_cases i
      exacts [row0, ha, hp, hb, hq, hc', hr]
    ext w
    simpa only [mem_row, tuple_two] using Finset.ext_iff.mp (rows_eq (w 0)) (w 1)
  have ok : feasible a b c p q r := by
    refine ⟨row_apart hc (i := 0) (j := 1) (by unfold cycleStep; decide) (.inl (by decide)) origin ha',
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact row_apart hc (i := 2) (j := 3) (by unfold cycleStep; decide) (.inl (by decide))
        (by simp [hp, pair]) hb'
    · exact row_apart hc (i := 2) (j := 3) (by unfold cycleStep; decide) (.inl (by decide))
        (by simp [hp, pair]) hb'
    · exact row_apart hc (i := 4) (j := 5) (by unfold cycleStep; decide) (.inl (by decide))
        (by simp [hq, pair]) hc''
    · exact row_apart hc (i := 4) (j := 5) (by unfold cycleStep; decide) (.inl (by decide))
        (by simp [hq, pair]) hc''
    · exact row_apart hc (i := 5) (j := 6) (by unfold cycleStep; decide) (.inl (by decide))
        hc'' (by simp [hr, pair])
    · exact row_apart hc (i := 5) (j := 6) (by unfold cycleStep; decide) (.inl (by decide))
        hc'' (by simp [hr, pair])
  exact ⟨_, eq.trans (patterns_checked a b c p q r ok)⟩

private def translateImage (s t : ZMod 7) (g : Isometry 2) : Isometry 2 :=
  (g.1, g.2.1, fun i => g.2.2 i + ![s,t] i)

theorem classify (C : Finset (Tuple 2)) (hc : packing cycleStep C) (hs : C.card = 10) :
    ∃ r : Fin 3, ∃ g : Isometry 2, C = actOnCode g (twoRepresentatives r) := by
  obtain ⟨s, t, hD, sizes, origin⟩ := normalize hc hs
  obtain ⟨v, hv⟩ := classify_normalized hD sizes origin
  let g := motion v.2
  have undo (x : Tuple 2) : act (translation s t) (act (translation (-s) (-t)) x) = x := by
    simp [translation_apply, tuple_two]
  have undoCode : actOnCode (translation s t) (actOnCode (translation (-s) (-t)) C) = C := by
    unfold actOnCode
    rw [Finset.image_image, show act (translation s t) ∘ act (translation (-s) (-t)) = id from funext undo,
      Finset.image_id]
  have comp (x : Tuple 2) :
      act (translation s t) (act g x) = act (translateImage s t g) x := by
    funext i
    simp [act, translation, translateImage, add_assoc]
  refine ⟨v.1, translateImage s t g, undoCode.symm.trans ?_⟩
  rw [hv]
  unfold actOnCode
  rw [Finset.image_image]
  exact Finset.image_congr (fun x _ => comp x)

theorem atlas_two (C : Finset (Tuple 2)) :
    (packing cycleStep C ∧ C.card = 10) ↔
      ∃ r : Fin 3, ∃ g : Isometry 2, C = actOnCode g (twoRepresentatives r) := by
  constructor
  · rintro ⟨hc, hs⟩
    exact classify C hc hs
  · rintro ⟨r, g, rfl⟩
    exact image_valid r g

/-- The old exhaustive checker returns true as a consequence of the proved classification. -/
theorem planar_classification : classificationCheck orbitIndices = true :=
  classificationCheck_of_orbits classify

end SevenCycle.Atlas.Planar.Kernel
