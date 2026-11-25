import HadwigerNelson.Angular.Runtime
import HadwigerNelson.Arithmetic.Rounding
import Mathlib.Tactic.Ring

namespace HadwigerNelson.Angular
open Arithmetic

theorem area_zero (tree : Segments) (h : tree.Valid) (d lo : Int)
    (hz : tree.stats.stop ≤ lo ∨ tree.stats.high ≤ d) : tree.area d lo = 0 := by
  induction tree with
  | single s => exact if_pos hz
  | branch t a b ia ib =>
    obtain ⟨rfl,ha,hb⟩ := h
    change max a.stats.stop b.stats.stop ≤ lo ∨ max a.stats.high b.stats.high ≤ d at hz
    have za : a.stats.stop ≤ lo ∨ a.stats.high ≤ d := by rcases hz with h|h <;> simp_all
    have zb : b.stats.stop ≤ lo ∨ b.stats.high ≤ d := by rcases hz with h|h <;> simp_all
    simp [Segments.area, ia ha za, ib hb zb]

private theorem area_full (tree : Segments) (h : tree.Valid) (d lo : Int)
    (hlo : lo ≤ tree.stats.start) (hd : d ≤ tree.stats.low) :
    tree.area d lo = tree.stats.mass-2*d*tree.stats.width := by
  induction tree with
  | single s =>
    change lo ≤ s.start at hlo
    change d ≤ min s.left s.right at hd
    have left : d ≤ s.left := (le_min_iff.mp hd).1
    have right : d ≤ s.right := (le_min_iff.mp hd).2
    have hstop : ¬s.stop ≤ lo := by change s.start < s.stop at h; omega
    simp only [Segments.area, Segment.area, Segments.stats, Segment.stats, hstop, false_or,
      if_pos hlo]
    split_ifs with small
    · have el : s.left = d := by have := (max_le_iff.mp small).1; omega
      have er : s.right = d := by have := (max_le_iff.mp small).2; omega
      rw [el,er]
      ring
    · rw [positiveArea2Up_full _ _ _ (by omega) (by omega)]
      ring
  | branch t a b ia ib =>
    obtain ⟨rfl,ha,hb⟩ := h
    change lo ≤ min a.stats.start b.stats.start at hlo
    change d ≤ min a.stats.low b.stats.low at hd
    rcases le_min_iff.mp hlo with ⟨la,lb⟩
    rcases le_min_iff.mp hd with ⟨da,db⟩
    change a.area d lo + b.area d lo =
      a.stats.mass+b.stats.mass-2*d*(a.stats.width+b.stats.width)
    rw [ia ha la da, ib hb lb db]
    ring

theorem Segments.fastArea_eq (tree : Segments) (ok : tree.Valid) (d lo : Int) :
    tree.fastArea d lo = tree.area d lo := by
  induction tree with
  | single => rfl
  | branch t a b ia ib =>
    dsimp only [fastArea]
    split_ifs with hz hf
    · exact (area_zero _ ok d lo hz).symm
    · exact (area_full _ ok d lo hf.1 hf.2).symm
    · rw [ia ok.2.1, ib ok.2.2]
      rfl

theorem tabulate_valid (widths : Array Nat) (step : Nat) (positive : 0 < step)
    (depth i : Nat) : (tabulate widths step depth i).Valid := by
  induction depth generalizing i with
  | zero =>
    change (i : Int)*step < ((i : Int)+1)*step
    have h : (0 : Int) < step := by exact_mod_cast positive
    rw [Int.add_mul, Int.one_mul]
    omega
  | succ depth ih => exact ⟨rfl,ih _,ih _⟩

end HadwigerNelson.Angular
