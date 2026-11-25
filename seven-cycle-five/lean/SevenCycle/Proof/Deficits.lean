import SevenCycle.Proof.Bands
import SevenCycle.Blueprint.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Deficits and full starts on an axis of a 113-word code

Three disjoint bands cover every level except the one at their common
reference residue. This gives the level formula directly from the
single-axis level count.
-/

namespace SevenCycle.Deficits

open Blueprint Proof

theorem sum_seven_at (f : ZMod 7 → ℕ) (i : ZMod 7) :
    ∑ j, f j = f i + (f (i+1) + (f (i+2) + (f (i+3) +
      (f (i+4) + (f (i+5) + f (i+6)))))) := by
  have all : (Finset.univ : Finset (ZMod 7)) = {0,1,2,3,4,5,6} := by decide
  calc
    ∑ j, f j = ∑ j : ZMod 7, f (i+j) := (Equiv.sum_comp (Equiv.addLeft i) f).symm
    _ = _ := by rw [all]; simp +decide

variable (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
variable (C : Finset (Tuple 4)) (hc : packing cycleStep C) (h113 : C.card = 113)

include h3 hc in
private theorem deficit_add_band (k : Fin 4) (i : ZMod 7) :
    deficit C k i + (band C k i).card = 33 :=
  Nat.sub_add_cancel (Bands.band_card_le h3 C hc k i)

include h3 hc h113 in
theorem deficit_sum (k : Fin 4) : ∑ i : ZMod 7, deficit C k i = 5 := by
  have hsum : ∑ i : ZMod 7, (deficit C k i + (band C k i).card) = 231 := by
    simp [deficit_add_band h3 C hc, ZMod.card]
  rw [Finset.sum_add_distrib] at hsum
  have hb : ∑ i : ZMod 7, (band C k i).card = 2 * C.card := Bands.sum_band_card C k
  omega

include h3 hc h113 in
theorem level_from_deficits (k : Fin 4) (i : ZMod 7) :
    (level C k i).card = 14 + deficit C k (i+1) + deficit C k (i+3) + deficit C k (i+5) := by
  have levels : ∑ j : ZMod 7, (level C k j).card = C.card := Bands.sum_level_card C k
  rw [sum_seven_at _ i] at levels
  have h1 := deficit_add_band h3 C hc k (i+1)
  have h3' := deficit_add_band h3 C hc k (i+3)
  have h5 := deficit_add_band h3 C hc k (i+5)
  have hb (j : ZMod 7) : (band C k j).card = (level C k j).card + (level C k (j+1)).card :=
    Bands.band_card C k j
  simp only [hb, add_assoc] at h1 h3' h5
  norm_num at h1 h3' h5
  omega


include h3 hc in
private theorem mem_full_iff_zero (k : Fin 4) (i : ZMod 7) :
    i ∈ fullStarts C k ↔ deficit C k i = 0 := by
  simp only [fullStarts, Finset.mem_filter, Finset.mem_univ, true_and]
  have := deficit_add_band h3 C hc k i
  omega

include h3 hc h113 in
theorem deficits_one (k : Fin 4) : 2 ≤ (fullStarts C k).card ∧
    ∀ i, 14 ≤ (level C k i).card ∧ (level C k i).card ≤ 19 := by
  have hs := deficit_sum h3 C hc h113 k
  constructor
  · let p (i : ZMod 7) := (band C k i).card = 33
    have hcount := (Finset.univ : Finset (ZMod 7)).card_filter_add_card_filter_not p
    have huniv : (Finset.univ : Finset (ZMod 7)).card = 7 := by decide
    have hbound : (Finset.univ.filter fun i => ¬p i).card ≤ ∑ i, deficit C k i := by
      rw [Finset.card_filter]
      apply Finset.sum_le_sum
      intro i _
      split
      · have := deficit_add_band h3 C hc k i
        unfold p at *
        omega
      · exact Nat.zero_le _
    change 2 ≤ (Finset.univ.filter p).card
    omega
  · intro i
    rw [sum_seven_at _ i] at hs
    rw [level_from_deficits h3 C hc h113 k i]
    omega

private def goodCentres (d : ZMod 7 → ℕ) : Prop :=
  (∃ i, d i = 0 ∧ d (i+1) = 0) →
    ∃ c, d (c-1) = 0 ∧ d c = 0 ∧ 2 ≤ d (c+1) + d (c+3) + d (c+5)

private instance (d : ZMod 7 → ℕ) : Decidable (goodCentres d) := by
  unfold goodCentres
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Each prefix uses at most the remaining deficit. The last entry is forced,
so the six bounded quantifiers visit exactly the 462 weak compositions of 5. -/
private theorem all_centres :
    ∀ (a : Fin 6) (b : Fin (6-a.val)) (c : Fin (6-a.val-b.val))
      (d : Fin (6-a.val-b.val-c.val)) (e : Fin (6-a.val-b.val-c.val-d.val))
      (f : Fin (6-a.val-b.val-c.val-d.val-e.val)),
      goodCentres ![a.val, b.val, c.val, d.val, e.val, f.val,
        5-a.val-b.val-c.val-d.val-e.val-f.val] := by decide +kernel

private theorem centres_of_sum (v : ZMod 7 → ℕ)
    (hs : v 0 + (v 1 + (v 2 + (v 3 + (v 4 + (v 5 + v 6))))) = 5) :
    goodCentres v := by
  have he := all_centres ⟨v 0, by omega⟩ ⟨v 1, by dsimp; omega⟩ ⟨v 2, by dsimp; omega⟩
    ⟨v 3, by dsimp; omega⟩ ⟨v 4, by dsimp; omega⟩ ⟨v 5, by dsimp; omega⟩
  have hlast : 5-v 0-v 1-v 2-v 3-v 4-v 5 = v 6 := by omega
  have hv : (![v 0, v 1, v 2, v 3, v 4, v 5, 5-v 0-v 1-v 2-v 3-v 4-v 5] :
      ZMod 7 → ℕ) = v := by
    funext i
    fin_cases i <;> first | rfl | exact hlast
  exact hv ▸ he


include h3 hc h113 in
theorem deficits_two (k : Fin 4) (h : ∃ i ∈ fullStarts C k, i+1 ∈ fullStarts C k) :
    ∃ c, HasCentre C k c := by
  have hs := deficit_sum h3 C hc h113 k
  rw [sum_seven_at _ 0] at hs
  simp only [zero_add] at hs
  obtain ⟨i, hi, hi'⟩ := h
  have full := mem_full_iff_zero h3 C hc k
  obtain ⟨c, hcprev, hcz, hcsize⟩ := centres_of_sum _ hs
    ⟨i, (full i).mp hi, (full _).mp hi'⟩
  have hlev := level_from_deficits h3 C hc h113 k c
  have hupper := ((deficits_one h3 C hc h113 k).2 c).2
  exact ⟨c, (full _).mpr hcprev, (full _).mpr hcz, by omega, hupper⟩

include h3 hc h113 in
theorem deficits_three_at (k : Fin 4) (i : ZMod 7)
    (h : ∀ t ∈ fullStarts C k, t+1 ∉ fullStarts C k)
    (h0 : i ∈ fullStarts C k) (h2 : i+2 ∈ fullStarts C k) :
    31 ≤ (band C k (i+1)).card := by
  have hn (j : ZMod 7) : deficit C k j ≠ 0 ∨ deficit C k (j+1) ≠ 0 := by
    by_cases hj : j ∈ fullStarts C k
    · exact Or.inr fun z => h j hj ((mem_full_iff_zero h3 C hc k _).mpr z)
    · exact Or.inl fun z => hj ((mem_full_iff_zero h3 C hc k _).mpr z)
  have z0 := (mem_full_iff_zero h3 C hc k _).mp h0
  have z2 := (mem_full_iff_zero h3 C hc k _).mp h2
  have h3' := hn (i+2)
  have h45 := hn (i+4)
  have h6 := hn (i+6)
  have wrap : (6 : ZMod 7) + 1 = 0 := by decide
  simp only [add_assoc, wrap, add_zero] at h3' h45 h6
  norm_num at h3' h45
  have hs := deficit_sum h3 C hc h113 k
  rw [sum_seven_at _ i] at hs
  have := deficit_add_band h3 C hc k (i+1)
  omega

include h3 hc h113 in
theorem deficits_three (k : Fin 4) (h : ∀ i ∈ fullStarts C k, i+1 ∉ fullStarts C k)
    (h0 : 0 ∈ fullStarts C k) (h2 : 2 ∈ fullStarts C k) : 31 ≤ (band C k 1).card :=
  deficits_three_at h3 C hc h113 k 0 h h0 h2

private theorem distance_range : ∀ x y : ZMod 7, x ≠ y →
    1 ≤ cycleDistance x y ∧ cycleDistance x y ≤ 3 := by
  unfold cycleDistance
  decide

private theorem axis_gap_exists {k : Fin 4} (h : 2 ≤ (fullStarts C k).card) :
    ∃ d : Fin 3, AxisGap C k (d.val + 1) := by
  let F := fullStarts C k
  let P := (F ×ˢ F).filter fun p => p.1 ≠ p.2
  have hp (i j : ZMod 7) : (i,j) ∈ P ↔ i ∈ F ∧ j ∈ F ∧ i ≠ j := by
    simp [P, and_assoc]
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h
  have hne : P.Nonempty := ⟨(i,j), (hp i j).mpr ⟨hi,hj,hij⟩⟩
  obtain ⟨⟨a,b⟩, hab, hmin⟩ :=
    P.exists_min_image (fun p => cycleDistance p.1 p.2) hne
  obtain ⟨ha, hb, hab'⟩ := (hp a b).mp hab
  obtain ⟨hlo,hhi⟩ := distance_range a b hab'
  refine ⟨⟨cycleDistance a b - 1, by omega⟩, ?_⟩
  change AxisGap C k (cycleDistance a b - 1 + 1)
  rw [Nat.sub_add_cancel hlo]
  exact ⟨⟨a, ha, b, hb, hab', rfl⟩, fun x hx y hy hxy =>
    hmin (x,y) ((hp x y).mpr ⟨hx,hy,hxy⟩)⟩

include h3 hc h113 in
theorem profile_exists : ∃ p, HasProfile C p := by
  choose d hd using fun k => axis_gap_exists C ((deficits_one h3 C hc h113 k).1)
  exact ⟨_, d, hd, rfl⟩

end SevenCycle.Deficits
