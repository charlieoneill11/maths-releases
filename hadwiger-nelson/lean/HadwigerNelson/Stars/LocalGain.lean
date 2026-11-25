import HadwigerNelson.Stars.Gain
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Option

namespace HadwigerNelson.Stars
noncomputable section

/-- Gain for a centre and its indexed neighbours. An edge listed in both
orientations contributes two incidences to its endpoints. -/
def localGain {L : Type*} {d : Nat} (center : Option L) (neighbor : Fin d → Option L) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => center.isSome = true ∧ center = neighbor j)).card : ℝ) -
    (if center.isSome = true ∧ ∀ a, ∃ j, neighbor j = some a then 1 else 0)

theorem localGain_range {L : Type*} {d : Nat} (c : Option L) (n : Fin d → Option L) :
    0 ≤ localGain c n ∧ localGain c n ≤ d := by
  classical
  let B := Finset.univ.filter (fun j => c.isSome = true ∧ c = n j)
  have size : B.card ≤ d := by simpa [B] using Finset.card_filter_le (Finset.univ : Finset (Fin d)) (fun j => c.isSome = true ∧ c = n j)
  have high : (B.card : ℝ) ≤ d := by exact_mod_cast size
  change 0 ≤ (B.card : ℝ) - _ ∧ _ ≤ (d : ℝ)
  by_cases h : c.isSome = true ∧ ∀ a, ∃ j, n j = some a
  · obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp h.1
    obtain ⟨j,hj⟩ := h.2 a
    have hj' : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,ha.trans hj.symm⟩
    have count : 1 ≤ B.card := Finset.card_pos.mpr ⟨j,hj'⟩
    have lo : (1:ℝ) ≤ B.card := by exact_mod_cast count
    simp only [localGain,if_pos h]
    change 0 ≤ (B.card : ℝ)-1 ∧ (B.card : ℝ)-1 ≤ d
    constructor <;> linarith
  · simp only [localGain,if_neg h,sub_zero]
    exact ⟨by positivity, high⟩

/-- Only equality, presence, and covering all colours enter the gain. -/
theorem localGain_relabel {L L' : Type*} {d : Nat} (e : L ≃ L') (c : Option L)
    (n : Fin d → Option L) :
    localGain (c.map e) (fun j => (n j).map e) = localGain c n := by
  classical
  have inj (x y : Option L) : x.map e = y.map e ↔ x=y := e.optionCongr.injective.eq_iff
  have cov : (∀ a : L', ∃ j, (n j).map e = some a) ↔ ∀ a : L, ∃ j, n j = some a := by
    constructor
    · intro h a
      obtain ⟨j,hj⟩ := h (e a)
      exact ⟨j,(inj _ (some a)).mp hj⟩
    · intro h a
      obtain ⟨j,hj⟩ := h (e.symm a)
      exact ⟨j,by simp [hj]⟩
  simp only [localGain,Option.isSome_map,inj,cov]

variable {V : Type*}

/-- The disjoint sum indexes each occurrence of v at either end. -/
def incidences (E : Finset (V × V)) (v : V) : Finset ((V × V) ⊕ (V × V)) := by
  classical exact (E.filter (fun e => v=e.1)).disjSum (E.filter (fun e => v=e.2))

def otherEnd : (V × V) ⊕ (V × V) → V := Sum.elim Prod.snd Prod.fst

theorem incidences_card (E : Finset (V × V)) (v : V) : (incidences E v).card = degree E v := by
  classical
  simp [incidences, degree, Finset.sum_add_distrib]

def incidenceEquiv (E : Finset (V × V)) (v : V) : Fin (degree E v) ≃ ↥(incidences E v) :=
  (Fintype.equivFinOfCardEq (by simp [incidences_card])).symm

theorem sees_iff_incidence (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) (a : Fin 6) :
    Sees E κ v a ↔ ∃ j, κ (otherEnd (incidenceEquiv E v j).val) = some a := by
  classical
  rw [(incidenceEquiv E v).exists_congr_right (q := fun j => κ (otherEnd j.val) = some a)]
  constructor
  · rintro ⟨e,he,h | h⟩
    · exact ⟨⟨Sum.inl e,by simp [incidences,he,h.1]⟩,h.2⟩
    · exact ⟨⟨Sum.inr e,by simp [incidences,he,h.1]⟩,h.2⟩
  · rintro ⟨⟨e,he⟩,hc⟩
    cases e with
    | inl e =>
      simp [incidences] at he
      exact ⟨e,he.1,Or.inl ⟨he.2.symm,hc⟩⟩
    | inr e =>
      simp [incidences] at he
      exact ⟨e,he.1,Or.inr ⟨he.2.symm,hc⟩⟩

theorem bad_incidence_iff (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V)
    (i : (V × V) ⊕ (V × V)) : i ∈ incidences (badEdges E κ) v ↔
    i ∈ incidences E v ∧ (κ v).isSome = true ∧ κ v = κ (otherEnd i) := by
  classical
  rcases i with ⟨a,b⟩ | ⟨a,b⟩
  · by_cases h : v = a
    · subst a
      simp [incidences,badEdges,Bad,otherEnd]
    · simp [incidences,h]
  · by_cases h : v = b
    · subst b
      cases hv : κ v <;> cases ha : κ a <;> simp [incidences,badEdges,Bad,otherEnd,hv,ha,eq_comm]
    · simp [incidences,h]

theorem gain_eq_local (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) :
    gain E κ v = localGain (κ v) (fun j => κ (otherEnd (incidenceEquiv E v j).val)) := by
  classical
  let en := incidenceEquiv E v
  have card : (Finset.univ.filter (fun j => (κ v).isSome = true ∧
      κ v = κ (otherEnd (en j).val))).card = sameCount E κ v := by
    rw [sameCount, ← incidences_card (badEdges E κ) v]
    apply Finset.card_bij (fun j _ => (en j).val)
    · intro j hj
      exact (bad_incidence_iff ..).2 ⟨(en j).property,(Finset.mem_filter.mp hj).2⟩
    · intro j _ k _ h
      exact en.injective (Subtype.ext h)
    · intro e he
      obtain ⟨inE,hc⟩ := (bad_incidence_iff ..).mp he
      let x : ↥(incidences E v) := ⟨e,inE⟩
      refine ⟨en.symm x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · simpa [x] using hc
      · simp [x]
  have lock : Locked E κ v ↔ (κ v).isSome = true ∧
      ∀ a, ∃ j, κ (otherEnd (en j).val) = some a := by simp only [Locked,sees_iff_incidence,en]
  change (sameCount E κ v : ℝ) - (locked E κ v : ℕ) = _
  rw [← card]
  unfold localGain locked
  rw [lock]
  split <;> norm_num [en] <;> apply congrArg Finset.card <;> ext j <;> simp

end
end HadwigerNelson.Stars
