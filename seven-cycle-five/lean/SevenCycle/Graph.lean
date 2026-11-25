import SevenCycle.Statement
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! The public code predicate is independence in the strong power of the seven-cycle. -/

namespace SevenCycle.Graph

/-- The strong product of n copies of G on words of length n. Its distinct
vertices are adjacent if their entries are equal or adjacent at every coordinate. -/
def strongPower {α : Type*} (G : SimpleGraph α) (n : ℕ) : SimpleGraph (Fin n → α) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm _ _ h := ⟨h.1.symm, fun i => (h.2 i).imp Eq.symm G.adj_symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The vertices of Mathlib's cycle on `Fin 7` are definitionally the residues of `ZMod 7`. -/
abbrev sevenCyclePower (n : ℕ) : SimpleGraph (Word n) := strongPower (SimpleGraph.cycleGraph 7) n

private theorem coordinate : ∀ a b : ZMod 7,
    (a = b ∨ (SimpleGraph.cycleGraph 7).Adj a b) ↔
      a-b ∈ ({-1, 0, 1} : Finset (ZMod 7)) := by
  simp only [SimpleGraph.cycleGraph_adj]
  decide

theorem adjacent_iff_confusable {n : ℕ} (x y : Word n) :
    (sevenCyclePower n).Adj x y ↔ Confusable x y := by
  change (x ≠ y ∧ ∀ i, x i = y i ∨ (SimpleGraph.cycleGraph 7).Adj (x i) (y i)) ↔ _
  simp only [Confusable, coordinate]

theorem isCode_iff_isIndepSet {n : ℕ} (C : Finset (Word n)) :
    IsCode C ↔ (sevenCyclePower n).IsIndepSet (C : Set (Word n)) := by
  constructor
  · intro hc x hx y hy _ h
    exact hc x hx y hy ((adjacent_iff_confusable x y).mp h)
  · intro hs x hx y hy h
    exact hs hx hy h.1 ((adjacent_iff_confusable x y).mpr h)

/-- A bound on all finite codes is precisely a bound on the graph's independence number. -/
theorem indepNum_le_iff (n b : ℕ) :
    (sevenCyclePower n).indepNum ≤ b ↔ ∀ C : Finset (Word n), IsCode C → C.card ≤ b := by
  constructor
  · intro h C hc
    exact ((isCode_iff_isIndepSet C).mp hc).card_le_indepNum.trans h
  · intro h
    obtain ⟨C, hc⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := sevenCyclePower n)
    rw [← hc.card_eq]
    exact h C ((isCode_iff_isIndepSet C).mpr hc.isIndepSet)

theorem indepNum_four_le_112 : (sevenCyclePower 4).indepNum ≤ 112 :=
  (indepNum_le_iff 4 112).mpr card_le_112

theorem indepNum_five_le_392 : (sevenCyclePower 5).indepNum ≤ 392 :=
  (indepNum_le_iff 5 392).mpr card_le_392

end SevenCycle.Graph
