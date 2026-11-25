import SevenCycle.TypeTwo.Matching
import SevenCycleRuntime.TypeTwoMatching

/-!
# Checking the middle levels of a type-two layout

The 33 bit positions index the edges of one perfect matching. Left and right
membership are recorded separately: seeing one endpoint does not determine
the membership of the other. Each input array gives the restrictions allowed
by one transverse band.
-/

namespace SevenCycle.TypeTwo

/-- The set of bit positions is used only to specify and prove the checker. -/
def indices (m : Mask) : Finset ℕ := (Finset.range 33).filter fun i => m.getLsbD i

private theorem countPrefix (m : Mask) (w : ℕ) :
    m.cpopNatRec w 0 = ((Finset.range w).filter fun i => m.getLsbD i).card := by
  induction w with
  | zero => simp
  | succ n ih =>
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, ih, Finset.range_add_one]
    by_cases h : m.getLsbD n <;> simp [Finset.filter_insert, h, Finset.mem_filter]

theorem pop_eq (m : Mask) : pop m = (indices m).card :=
  (BitVec.toNat_cpop m).trans (countPrefix m 33)

/-- A band or a prefix records precisely the true left/right bits at seen sites. -/
def Realizes (x y : Mask) (a : Mark) : Prop :=
  a.leftIn = a.leftSeen &&& x ∧ a.rightIn = a.rightSeen &&& y

/-- These bounds concern the full middle levels, counted in matching-edge order. -/
def Legal (x y : Mask) : Prop :=
  x &&& y = 0 ∧ pop (~~~(x ||| y)) ≤ 2 ∧
    14 ≤ pop x ∧ pop x ≤ 19 ∧ 14 ≤ pop y ∧ pop y ≤ 19

private theorem agree_true (s t x : Mask) : agreeOn s t (s &&& x) (t &&& x) := by
  simp only [agreeOn, beq_iff_eq]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, show (0 : Mask)[i] = false from BitVec.getElem_zero hi]
  cases s[i] <;> cases t[i] <;> cases x[i] <;> rfl

theorem agrees_of_realizes {x y : Mask} {a b : Mark}
    (ha : Realizes x y a) (hb : Realizes x y b) : agrees a b := by
  simp [agrees, ha.1, ha.2, hb.1, hb.2, agree_true]

theorem combine_realizes {x y : Mask} {a b : Mark}
    (ha : Realizes x y a) (hb : Realizes x y b) : Realizes x y (combine a b) := by
  simp [Realizes, combine, ha.1, ha.2, hb.1, hb.2, BitVec.and_or_distrib_right]

private theorem pop_mono {a b : Mask} (h : ∀ i < 33, a.getLsbD i → b.getLsbD i) :
    pop a ≤ pop b := by
  rw [pop_eq, pop_eq]
  exact Finset.card_le_card (by
    intro i hi
    obtain ⟨hi, ha⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi, h i (Finset.mem_range.mp hi) ha⟩)

private theorem pop_and_le (a b : Mask) : pop (a &&& b) ≤ pop b := by
  apply pop_mono
  simp

private theorem restrict_neg (seen v : Mask) :
    seen &&& ~~~(seen &&& v) = seen &&& ~~~v := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not]
  cases seen[i] <;> cases v[i] <;> rfl

private theorem restrict_double (s t x y : Mask) :
    (s &&& x) &&& (t &&& y) = (s &&& t) &&& (x &&& y) := by
  ac_rfl

private theorem restrict_empty (s t x y : Mask) :
    s &&& t &&& ~~~((s &&& x) ||| (t &&& y)) = (s &&& t) &&& ~~~(x ||| y) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
  cases s[i] <;> cases t[i] <;> cases x[i] <;> cases y[i] <;> rfl

theorem viable_of_realizes {x y : Mask} {a : Mark}
    (h : Legal x y) (ha : Realizes x y a) : viable a := by
  obtain ⟨hd, he, hxmin, hxmax, hymin, hymax⟩ := h
  have hx := pop_and_le a.leftSeen (~~~x)
  have hy := pop_and_le a.rightSeen (~~~y)
  have hx' : pop (~~~x) = 33 - pop x := BitVec.toNat_cpop_not
  have hy' : pop (~~~y) = 33 - pop y := BitVec.toNat_cpop_not
  have hab : (a.leftSeen &&& x) &&& (a.rightSeen &&& y) = 0 := by
    rw [restrict_double, hd]
    exact BitVec.and_zero
  simp only [viable, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    ha.1, ha.2, restrict_empty, restrict_neg]
  exact ⟨⟨⟨⟨⟨hab, (pop_and_le _ _).trans he⟩, (pop_and_le _ _).trans hxmax⟩,
    (pop_and_le _ _).trans hymax⟩, by omega⟩, by omega⟩

private theorem hasPrefix_of_realizes (bands : Array (Array Mark)) (x y : Mask) (h : Legal x y)
    (hb : ∀ i : Fin bands.size, ∃ b ∈ bands[i], Realizes x y b) (n : ℕ) (hn : n ≤ bands.size)
    (a : Mark) (ha : Realizes x y a) : hasPrefix bands n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hi : n < bands.size := hn
    obtain ⟨b, hmem, hreal⟩ := hb ⟨n,hi⟩
    rw [hasPrefix, Array.getElem?_eq_getElem hi]
    apply Array.any_eq_true'.mpr
    refine ⟨b, hmem, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨agrees_of_realizes ha hreal, viable_of_realizes h (combine_realizes ha hreal)⟩,
      ih (by omega) _ (combine_realizes ha hreal)⟩

/-- Rejection excludes every assignment satisfying the matching and level bounds
for which each marked band supplies its true restriction. -/
theorem rejectsLayout_sound (bands : Array (Array Mark)) (hc : rejectsLayout bands = true) :
    ¬ ∃ x y, Legal x y ∧ ∀ i : Fin bands.size, ∃ b ∈ bands[i], Realizes x y b := by
  rintro ⟨x,y,h,hb⟩
  have hpass := hasPrefix_of_realizes bands x y h hb bands.size le_rfl empty
    (by simp [Realizes, empty])
  simp [rejectsLayout, hpass] at hc

end SevenCycle.TypeTwo
