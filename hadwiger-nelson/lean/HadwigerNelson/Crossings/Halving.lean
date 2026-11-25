import HadwigerNelson.Crossings.Subsets
import HadwigerNelson.Crossings.Parameters
import HadwigerNelson.Crossings.FairBits

/-! Independently take one of the two edge slots at each ordered endpoint pair. -/
namespace HadwigerNelson.Crossings
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ParallelSlots

def key {n m : ℕ} (G : Graph n m) (e : Fin m) := (G.left e,G.right e)
def bit {n m : ℕ} (G : Graph n m) (e : Fin m) : Bool :=
  decide (∃ f, f < e ∧ key G f = key G e)

theorem parallel_bits {n m : ℕ} (G : Graph n m) (hm : ∀ v w, multiplicity G v w ≤ 2)
    {e f : Fin m} (ne : e ≠ f) (same : key G e = key G f) : bit G e ≠ bit G f := by
  have forward {i j : Fin m} (lt : i < j) (eq : key G i = key G j) : bit G i = false ∧ bit G j = true := by
    constructor
    · simp only [bit, decide_eq_false_iff_not]
      rintro ⟨h,hi,he⟩
      let S := Finset.univ.filter fun a : Fin m ↦ G.left a = G.left j ∧ G.right a = G.right j
      have mem {a : Fin m} (h : key G a = key G j) : a ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst h, congrArg Prod.snd h⟩
      have sub : ({h,i,j} : Finset (Fin m)) ⊆ S := by
        simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using
          And.intro (mem (he.trans eq)) (And.intro (mem eq) (mem (a:=j) rfl))
      have bound := (Finset.card_le_card sub).trans (hm (G.left j) (G.right j))
      simp [hi.ne,lt.ne,(hi.trans lt).ne] at bound
    · exact decide_eq_true ⟨i,lt,eq⟩
  rcases lt_or_gt_of_ne ne with h|h
  · obtain ⟨a,b⟩ := forward h same
    simp [a,b]
  · obtain ⟨a,b⟩ := forward h same.symm
    simp [a,b]

end ParallelSlots

open ParallelSlots

/-- Lemma 28, for any drawing with finite pairwise intersections. -/
theorem half_from_sample (facts : CitedFacts) {n m k : ℕ} (G : Graph n (2*m)) (D : Drawing G)
    (hk : 4 ≤ k) (hkn : k ≤ n) (hm : ∀ v w, multiplicity G v w ≤ 2)
    (hd : D.FiniteIntersections)
    (sample : ∀ {l} (g : Graph n l), g.IsSimple → sampledLower n k l ≤ crossingNumber g) :
    4*sampledLower n k m ≤ D.crossingCount := by
  classical
  let Ω := (Fin n × Fin n) → Bool
  let A : Finset Ω := Finset.univ
  let keep (w : Ω) (e : Fin (2*m)) := w (key G e) = bit G e
  let E (w : Ω) := Finset.univ.filter (keep w)
  let C := events D hd
  let survive (w : Ω) (p : Fin (2*m) × Fin (2*m) × Plane) := keep w p.1 ∧ keep w p.2.1
  let retained (w : Ω) := (C.filter (survive w)).card
  have single (w : Ω) : (Selection.spanning G (E w)).graph.IsSimple := by
    let s := Selection.spanning G (E w)
    intro i j hij
    apply s.edge.injective
    by_contra ne
    have eq : key G (s.edge i) = key G (s.edge j) := hij
    have hit (t : Fin (E w).card) : w (key G (s.edge t)) = bit G (s.edge t) :=
      (Finset.mem_filter.mp ((E w).orderEmbOfFin_mem rfl t)).2
    exact parallel_bits G hm ne eq ((hit i).symm.trans ((congrArg w eq).trans (hit j)))
  have totalE : 2 * (∑ w ∈ A, (E w).card) = 2*m*A.card := by
    unfold E
    rw [sum_filter_card, Finset.mul_sum]
    have each (e : Fin (2*m)) : 2*(A.filter (fun w ↦ keep w e)).card = A.card :=
      fair_one (key G e) (bit G e)
    simp_rw [each]
    simp
  have totalC : 4 * (∑ w ∈ A, retained w) ≤ D.crossingCount*A.card := by
    unfold retained
    rw [sum_filter_card,Finset.mul_sum]
    calc
      _ ≤ ∑ _p ∈ C, A.card := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases h : key G p.1 = key G p.2.1
        · have neq := parallel_bits G hm ((mem_events _ _ _).mp hp).1.ne h
          have empty : (A.filter fun w ↦ survive w p) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            obtain ⟨a,b⟩ := (Finset.mem_filter.mp hw).2
            exact neq (a.symm.trans ((congrArg w h).trans b))
          simp [empty]
        · exact (fair_two _ _ h _ _).le
      _ = _ := by simp [C]
  have p4pos := fourProbability_pos hk hkn
  have per (w : Ω) : 6*((E w).card:ℝ)*pairProbability n k-(266/9:ℝ)*(k-2:ℝ) ≤
      (retained w:ℝ)*fourProbability n k := by
    let s := Selection.spanning G (E w)
    have l := sample s.graph (single w)
    have dg := facts.le_drawing s.graph (single w) (s.drawing D) (s.finite D hd)
    have cnt := s.count_le_filter D hd (keep w)
      (fun e ↦ (Finset.mem_filter.mp ((E w).orderEmbOfFin_mem rfl e)).2)
    have cmp : (crossingNumber s.graph : ℝ) ≤ retained w := by exact_mod_cast dg.trans cnt
    exact (div_le_iff₀ p4pos).mp (l.trans cmp)
  have sum := Finset.sum_le_sum (fun w (_ : w ∈ A) ↦ per w)
  rw [Finset.sum_sub_distrib, ←Finset.sum_mul, ←Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    ←Finset.sum_mul] at sum
  have mean : (∑ w ∈ A, ((E w).card : ℝ)) = (m : ℝ)*A.card := by
    have lifted : 2*(∑ w ∈ A, ((E w).card : ℝ)) = 2*(m:ℝ)*A.card := by exact_mod_cast totalE
    linarith
  have cross : 4*(∑ w ∈ A, (retained w:ℝ)) ≤ (D.crossingCount:ℝ)*A.card := by exact_mod_cast totalC
  have pos : (0:ℝ) < A.card := by exact_mod_cast (Finset.card_pos.mpr ⟨fun _ ↦ false,Finset.mem_univ _⟩ : 0 < A.card)
  rw [mean] at sum
  unfold sampledLower
  rw [← mul_div_assoc]
  apply (div_le_iff₀ p4pos).mpr
  apply (le_of_mul_le_mul_left _ pos)
  nlinarith only [sum, mul_le_mul_of_nonneg_right cross p4pos.le]

end
end HadwigerNelson.Crossings
