import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The finite counting and recolouring argument of Lemma 20. Both incident
ends are counted, so an input may list either orientation of an edge. -/

open scoped BigOperators

namespace HadwigerNelson.Stars

variable {V : Type*}

/-- Both ends have the same nonblank colour. -/
def Bad (κ : V → Option (Fin 6)) (e : V × V) : Prop :=
  (κ e.1).isSome = true ∧ κ e.1 = κ e.2

noncomputable def badEdges (E : Finset (V × V)) (κ : V → Option (Fin 6)) : Finset (V × V) := by
  classical exact E.filter (Bad κ)

noncomputable def badCount (E : Finset (V × V)) (κ : V → Option (Fin 6)) : ℕ :=
  (badEdges E κ).card

/-- Some listed edge joins the vertex to a neighbour of colour k. -/
def Sees (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) (k : Fin 6) : Prop :=
  ∃ e ∈ E, (e.1 = v ∧ κ e.2 = some k) ∨ (e.2 = v ∧ κ e.1 = some k)

def Locked (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) : Prop :=
  (κ v).isSome = true ∧ ∀ k, Sees E κ v k

noncomputable def locked (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) : ℕ := by
  classical exact if Locked E κ v then 1 else 0

/-- Degree in the given edge list, with one contribution from either end. -/
noncomputable def degree (E : Finset (V × V)) (v : V) : ℕ := by
  classical exact ∑ e ∈ E, ((if v = e.1 then 1 else 0) + (if v = e.2 then 1 else 0))

noncomputable def sameCount (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) : ℕ :=
  degree (badEdges E κ) v

theorem sum_degree (S : Finset V) (E : Finset (V × V))
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) :
    ∑ v ∈ S, degree E v = 2 * E.card := by
  classical
  unfold degree
  rw [Finset.sum_comm]
  calc
    _ = ∑ _e ∈ E, (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq', (ends e he).1, (ends e he).2]
    _ = _ := by simp [Nat.mul_comm]

theorem sum_sameCount (S : Finset V) (E : Finset (V × V)) (κ : V → Option (Fin 6))
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) :
    ∑ v ∈ S, sameCount E κ v = 2 * badCount E κ := by
  classical
  apply sum_degree
  intro e he
  exact ends e (Finset.mem_filter.mp he).1

/-- If every bad edge touches v, a colour absent from its neighbourhood repairs
all bad edges by recolouring just v. -/
private theorem locked_of_bad_edges_touch {S : Finset V} {E : Finset (V × V)}
    {κ : V → Option (Fin 6)} {v : V} (hv : v ∈ S)
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (full : ∀ x ∈ S, (κ x).isSome = true)
    (impossible : ¬ ∃ c : V → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2)
    (touch : ∀ e ∈ E, Bad κ e → e.1 = v ∨ e.2 = v) : Locked E κ v := by
  classical
  refine ⟨full v hv, fun k => ?_⟩
  by_contra absent
  let c (x : V) := (κ x).getD 0
  have val (x : V) (hx : x ∈ S) : κ x = some (c x) := by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (full x hx)
    simp [c, ha]
  apply impossible
  refine ⟨fun x => if x = v then k else c x, ?_⟩
  intro e he equal
  by_cases l : e.1 = v
  · have r : e.2 ≠ v := fun h => loops e he (l.trans h.symm)
    simp only [if_pos l, if_neg r] at equal
    exact absent ⟨e, he, Or.inl ⟨l, (val _ (ends e he).2).trans (congrArg some equal.symm)⟩⟩
  by_cases r : e.2 = v
  · simp only [if_neg l, if_pos r] at equal
    exact absent ⟨e, he, Or.inr ⟨r, (val _ (ends e he).1).trans (congrArg some equal)⟩⟩
  simp only [if_neg l, if_neg r] at equal
  have mono : Bad κ e := ⟨full _ (ends e he).1, by rw [val _ (ends e he).1, val _ (ends e he).2, equal]⟩
  exact (touch e he mono).elim l r

/-- Lemma 20, multiplied by four. The forest supplies exactly the condition
on Y used in the proof: a blank vertex leaves at least one blank component. -/
theorem one_bad_edge (S : Finset V) (E : Finset (V × V)) (κ : V → Option (Fin 6)) (Y : ℕ)
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (blank_component : (∃ v ∈ S, κ v = none) → 1 ≤ Y)
    (impossible : ¬ ∃ c : V → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2) :
    4 ≤ 4 * Y + 2 * badCount E κ + ∑ v ∈ S, locked E κ v := by
  classical
  by_cases hy : 1 ≤ Y
  · omega
  have full (v : V) (hv : v ∈ S) : (κ v).isSome = true := by
    cases h : κ v with
    | none => exact False.elim (hy (blank_component ⟨v, hv, h⟩))
    | some _ => rfl
  by_cases many : 2 ≤ badCount E κ
  · omega
  have nonempty : (badEdges E κ).Nonempty := by
    by_contra empty
    apply impossible
    refine ⟨fun v => (κ v).getD 0, ?_⟩
    intro e he equal
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (full _ (ends e he).1)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (full _ (ends e he).2)
    simp only [ha, hb, Option.getD_some] at equal
    exact empty ⟨e, Finset.mem_filter.mpr ⟨he, full _ (ends e he).1, by rw [ha, hb, equal]⟩⟩
  have hcard : (badEdges E κ).card = 1 := by
    have := Finset.card_pos.mpr nonempty
    change ¬ 2 ≤ (badEdges E κ).card at many
    omega
  obtain ⟨e, sole⟩ := Finset.card_eq_one.mp hcard
  have element : e ∈ badEdges E κ := by simp [sole]
  have he := (Finset.mem_filter.mp element).1
  have unique (f : V × V) (hf : f ∈ E) (hm : Bad κ f) : f = e := by
    have mem : f ∈ badEdges E κ := Finset.mem_filter.mpr ⟨hf, hm⟩
    simpa [sole] using mem
  have left := locked_of_bad_edges_touch (ends e he).1 ends loops full impossible
    (fun f hf hm => Or.inl (congrArg Prod.fst (unique f hf hm)))
  have right := locked_of_bad_edges_touch (ends e he).2 ends loops full impossible
    (fun f hf hm => Or.inr (congrArg Prod.snd (unique f hf hm)))
  have two : 2 ≤ (S.filter (Locked E κ)).card := by
    exact Finset.one_lt_card_iff.mpr ⟨e.1, e.2, Finset.mem_filter.mpr ⟨(ends e he).1, left⟩,
      Finset.mem_filter.mpr ⟨(ends e he).2, right⟩, loops e he⟩
  have count : ∑ v ∈ S, locked E κ v = (S.filter (Locked E κ)).card := by
    simp only [locked, Finset.card_filter]
  change (badEdges E κ).card = 1 at hcard
  simp only [badCount, hcard, count]
  omega

/-- Every locked nonblank vertex is incident to a bad edge. -/
theorem locked_le_sameCount (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) :
    locked E κ v ≤ sameCount E κ v := by
  classical
  by_cases h : Locked E κ v
  · obtain ⟨k, hv⟩ := Option.isSome_iff_exists.mp h.1
    obtain ⟨e, he, hed⟩ := h.2 k
    have hb : Bad κ e := by
      rcases hed with ⟨r,c⟩ | ⟨r,c⟩
      · simp [Bad,r,hv,c]
      · simp [Bad,r,hv,c]
    have hi : e ∈ badEdges E κ := Finset.mem_filter.mpr ⟨he,hb⟩
    have hn : 1 ≤ ((if v = e.1 then 1 else 0) + (if v = e.2 then 1 else 0) : ℕ) := by
      rcases hed with ⟨r,_⟩ | ⟨r,_⟩
      · simp [r]
      · simp [r]
    simp only [locked, if_pos h, sameCount, degree]
    exact hn.trans (Finset.single_le_sum (f := fun f : V × V =>
      (if v = f.1 then 1 else 0) + (if v = f.2 then 1 else 0))
      (fun f _ => Nat.zero_le _) hi)
  · simp [locked,h]

end HadwigerNelson.Stars
