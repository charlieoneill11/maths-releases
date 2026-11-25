import HadwigerNelson.Centres.ThresholdPairs
import HadwigerNelson.Centres.ArcIncidences
import HadwigerNelson.Centres.DoubleTotals

/-! The long single-arc count at each of the seven thresholds of Lemma 51.
Internal pairs and the two independent complement bounds retain their exact
integer rounding. -/

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem count_directions {X : Finset Plane} (hd : minNonisolatedDegree X 3)
    (S : Finset (Arc X)) (T : Finset (Plane×Plane)) (single : ∀ e∈S, ¬paired e)
    (maps : ∀ e∈S, ∀ b : Bool, ends e b∈T) : 2*S.card ≤ T.card := by
  let domain := S×ˢ(univ : Finset Bool)
  let f (s : Arc X × Bool) := ends s.1 s.2
  have card : domain.card≤T.card := by
    apply card_le_card_of_injOn f
    · intro z hz
      exact maps z.1 (mem_product.mp hz).1 z.2
    · intro a ha b _ eq
      have h := ends_single_injective hd (single _ (mem_product.mp ha).1) eq
      exact Prod.ext h.1 h.2
  simpa [domain,mul_comm] using card

theorem longSingles_lower (X D : Finset Plane) (sub : D⊆X) (sep : Packing.separated D δ)
    (hd : minNonisolatedDegree X 3) (i : Fin 7) :
    2*(unitEdgeCount X:ℝ)-2*(doubledPairs X:ℝ)-
      ((((diskLimit i-1)*D.card/2:ℕ):ℝ) + min (2*(outsideDegree X D:ℝ))
        (((diskLimit i*(X.card-D.card)+(X.card-D.card).choose 2):ℕ):ℝ)) ≤ (longSingles X i).card := by
  let r := threshold i
  let singles := (univ : Finset (Arc X)).filter (fun e => ¬paired e)
  let short := singles.filter (fun e => dist (start e) (finish e)<r)
  let inside := short.filter (fun e => start e∈D ∧ finish e∈D)
  let outer := short.filter (fun e => ¬(start e∈D ∧ finish e∈D))
  have singly {e} (h : e∈short) : ¬paired e := (mem_filter.mp (mem_filter.mp h).1).2
  have length {e} (h : e∈short) : dist (start e) (finish e)<r := (mem_filter.mp h).2
  have inner_bound : inside.card≤(diskLimit i-1)*D.card/2 := by
    have count := count_directions hd inside (closeOrdered D D r) (fun _ h => singly (mem_filter.mp h).1)
      (fun e he b => by
        obtain ⟨sh,h⟩ := mem_filter.mp he
        apply mem_filter.mpr
        have direction := ends_consecutive hd e b
        refine ⟨?_,direction.1,(ends_dist e b).trans_lt (length sh)⟩
        cases b
        · exact mem_product.mpr h
        · exact mem_product.mpr h.symm)
    have u := count.trans (inside_pair_cap D sep i)
    exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by omega)
  have outside_pairs : outer.card ≤ diskLimit i*(X.card-D.card)+(X.card-D.card).choose 2 := by
    have count := count_directions hd outer (outsideClose X D r) (fun _ h => singly (mem_filter.mp h).1)
      (fun e he b => by
        obtain ⟨sh,h⟩ := mem_filter.mp he
        apply mem_filter.mpr
        refine ⟨mem_filter.mpr ⟨mem_product.mpr (ends_mem e b),(ends_consecutive hd e b).1,
          (ends_dist e b).trans_lt (length sh)⟩,?_⟩
        cases b <;> simp only [ends,Bool.false_eq_true,if_false,if_true] <;> tauto)
    have u := count.trans (outside_pair_cap X D sub sep i)
    omega
  have outside_inc : outer.card ≤ 2*outsideDegree X D := by
    apply le_trans _ (card_touched_le X (X\D) hd sdiff_subset)
    apply card_le_card
    intro e he
    have h := (mem_filter.mp he).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    by_cases a : start e∈D
    · exact Or.inr (mem_sdiff.mpr ⟨finish_mem e,fun b => h ⟨a,b⟩⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨start_mem e,a⟩)
  have all := (univ : Finset (Arc X)).card_filter_add_card_filter_not paired
  change (pairedArcs X).card+singles.card=(univ : Finset (Arc X)).card at all
  rw [card_all_arcs X] at all
  have splits := singles.card_filter_add_card_filter_not (fun e => dist (start e) (finish e)<r)
  have eq : (singles.filter fun e => ¬dist (start e) (finish e)<r)=longSingles X i := by
    simp only [singles,filter_filter,longSingles,not_lt,r]
  rw [eq] at splits
  change short.card+(longSingles X i).card=singles.card at splits
  have split := short.card_filter_add_card_filter_not (fun e => start e∈D ∧ finish e∈D)
  change inside.card+outer.card=short.card at split
  have total : 2*unitEdgeCount X ≤ 2*doubledPairs X + (diskLimit i-1)*D.card/2 + outer.card + (longSingles X i).card := by
    have paired := paired_le_twice X hd
    omega
  have tr : 2*(unitEdgeCount X:ℝ) ≤ 2*(doubledPairs X:ℝ) + ((((diskLimit i-1)*D.card/2):ℕ):ℝ) +
      (outer.card:ℝ) + ((longSingles X i).card:ℝ) := by exact_mod_cast total
  have ob : (outer.card:ℝ) ≤ min (2*(outsideDegree X D:ℝ)) (((diskLimit i*(X.card-D.card)+(X.card-D.card).choose 2):ℕ):ℝ) :=
    le_min (by exact_mod_cast outside_inc) (by exact_mod_cast outside_pairs)
  linarith

end
end HadwigerNelson.Centres
