import SevenCycle.Proof.Model
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Levels, bands and the bound in one higher dimension

Deleting a fixed coordinate maps each band to a code of the same size.
Summing the resulting inequalities counts each word exactly twice.
-/

namespace SevenCycle.Bands

open Proof

def dropCoord {n : ℕ} (k : Fin (n+1)) (x : Tuple (n+1)) : Tuple n :=
  fun j => x (k.succAbove j)

def level {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1)) (i : ZMod 7) :=
  C.filter fun x => x k = i

def band {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1)) (i : ZMod 7) :=
  C.filter fun x => x k = i ∨ x k = i + 1

private theorem step_within_band {a b i : ZMod 7}
    (ha : a = i ∨ a = i + 1) (hb : b = i ∨ b = i + 1) : cycleStep a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [cycleStep]

/-- Any two words of the band which agree or are close on the surviving axes are equal. -/
private theorem eq_of_close_projection {n : ℕ} {C : Finset (Tuple (n+1))}
    (hc : packing cycleStep C) {k : Fin (n+1)} {i : ZMod 7} {x y : Tuple (n+1)}
    (hx : x ∈ band C k i) (hy : y ∈ band C k i)
    (h : ∀ j, cycleStep (dropCoord k x j) (dropCoord k y j)) : x = y := by
  obtain ⟨hxC, hxk⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyC, hyk⟩ := Finset.mem_filter.mp hy
  by_contra hne
  exact hc x hxC y hyC ⟨hne, (Fin.forall_iff_succAbove k).mpr ⟨step_within_band hxk hyk, h⟩⟩

theorem band_projection {n : ℕ} {C : Finset (Tuple (n+1))} (hc : packing cycleStep C)
    (k : Fin (n+1)) (i : ZMod 7) :
    Set.InjOn (dropCoord k) (band C k i : Set (Tuple (n+1))) ∧
      packing cycleStep ((band C k i).image (dropCoord k)) := by
  constructor
  · intro x hx y hy he
    apply eq_of_close_projection hc hx hy
    intro j
    rw [he]
    simp [cycleStep]
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hxy.1 (congrArg _ (eq_of_close_projection hc ha hb hxy.2))

theorem band_card {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1)) (i : ZMod 7) :
    (band C k i).card = (level C k i).card + (level C k (i+1)).card := by
  unfold band level
  rw [Finset.filter_or]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have he := (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
  have : (0 : ZMod 7) = 1 := add_left_cancel (by simpa using he : i + 0 = i + 1)
  exact (by decide : (0 : ZMod 7) ≠ 1) this

theorem sum_level_card {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1)) :
    ∑ i : ZMod 7, (level C k i).card = C.card := by
  exact (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _).symm

theorem sum_band_card {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1)) :
    ∑ i : ZMod 7, (band C k i).card = 2 * C.card := by
  have hshift : ∑ i : ZMod 7, (level C k (i+1)).card = ∑ i : ZMod 7, (level C k i).card :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod 7)) fun i => (level C k i).card
  simp_rw [band_card]
  rw [Finset.sum_add_distrib, hshift, sum_level_card, two_mul]

theorem alternating_band_sum {n : ℕ} (C : Finset (Tuple (n+1))) (k : Fin (n+1))
    (i : ZMod 7) : 2 * ((level C k i).card : ℤ) =
      ∑ j : Fin 7, (-1 : ℤ) ^ j.val * ((band C k (i + (j.val : ZMod 7))).card : ℤ) := by
  have univ7 : (Finset.univ : Finset (Fin 7)) = {0,1,2,3,4,5,6} := by decide
  rw [univ7]
  have wrap : (6 : ZMod 7) + 1 = 0 := by decide
  simp [band_card, add_assoc, wrap]
  norm_num
  omega

theorem band_card_le {n a : ℕ} (ha : ∀ D : Finset (Tuple n), packing cycleStep D → D.card ≤ a)
    (C : Finset (Tuple (n+1))) (hc : packing cycleStep C) (k : Fin (n+1)) (i : ZMod 7) :
    (band C k i).card ≤ a := by
  obtain ⟨hinj, hcode⟩ := band_projection hc k i
  rw [← Finset.card_image_iff.mpr hinj]
  exact ha _ hcode

theorem band_bound {n a : ℕ} (ha : ∀ D : Finset (Tuple n), packing cycleStep D → D.card ≤ a)
    (C : Finset (Tuple (n+1))) (hc : packing cycleStep C) : C.card ≤ 7 * a / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  calc
    C.card * 2 = ∑ i : ZMod 7, (band C 0 i).card := by rw [sum_band_card, Nat.mul_comm]
    _ ≤ ∑ _ : ZMod 7, a := Finset.sum_le_sum fun i _ => band_card_le ha C hc 0 i
    _ = 7 * a := by simp [ZMod.card]

end SevenCycle.Bands
