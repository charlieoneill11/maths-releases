import HadwigerNelson.Angular.Bins
import HadwigerNelson.Arithmetic.Rays

namespace HadwigerNelson.Angular
open Arithmetic

private theorem ediv_mono_frac {a b c d : Int} (hb : 0 < b) (hd : 0 < d)
    (h : (a:ℝ)/b ≤ (c:ℝ)/d) : a/b ≤ c/d := by
  have l := (floorDiv_le_real a hb).trans h
  have hh : (↑(a/b) : ℝ) < ↑(c/d)+1 := lt_of_le_of_lt l (real_lt_floorDiv_add_one c hd)
  have hi : a/b < c/d+1 := by exact_mod_cast hh
  omega

private theorem ceil_mono_frac {a b c d : Int} (hb : 0 < b) (hd : 0 < d)
    (h : (a:ℝ)/b ≤ (c:ℝ)/d) : ceilDiv a b ≤ ceilDiv c d := by
  have l := h.trans (real_le_ceilDiv c hd)
  have hh : (ceilDiv a b : ℝ) < (ceilDiv c d : ℝ)+1 :=
    (ceilDiv_lt_real_add_one a hb).trans_le (by linarith)
  have hi : ceilDiv a b < ceilDiv c d+1 := by exact_mod_cast hh
  omega

/-- All four outward bounds contract when the interval of parameter indices shrinks. -/
theorem halfAngleBox_refines {n i j k l : Nat} (hn : 0 < n) (hik : i ≤ k)
    (hkl : k ≤ l) (hlj : l ≤ j) (hj : j ≤ n) :
    (halfAngleBox n i j).xlo ≤ (halfAngleBox n k l).xlo ∧
    (halfAngleBox n k l).xhi ≤ (halfAngleBox n i j).xhi ∧
    (halfAngleBox n i j).ylo ≤ (halfAngleBox n k l).ylo ∧
    (halfAngleBox n k l).yhi ≤ (halfAngleBox n i j).yhi := by
  let S : Int := CompleteWave.scale
  have hn' : (0:Int) < n := by exact_mod_cast hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hS : (0:ℝ) ≤ S := by dsimp [S]; positivity
  have ord {a b:Nat} (h : a ≤ b) : (a:ℝ)/n ≤ (b:ℝ)/n :=
    div_le_div_of_nonneg_right (by exact_mod_cast h) hnR.le
  have last : (j:ℝ)/n ≤ 1 := (div_le_one hnR).2 (by exact_mod_cast hj)
  have cm {a b:Nat} (h : a ≤ b) :
      (rayXNum S n b : ℝ) / (rayDen n b : ℝ) ≤
      (rayXNum S n a : ℝ) / (rayDen n a : ℝ) := by
    rw [← scaled_rayX S _ _ hn', ← scaled_rayX S _ _ hn']
    push_cast
    exact mul_le_mul_of_nonneg_left (rayX_antitone (by positivity) (ord h)) hS
  have sm {a b:Nat} (h : a ≤ b) (hb : b ≤ j) :
      (rayYNum S n a : ℝ) / (rayDen n a : ℝ) ≤
      (rayYNum S n b : ℝ) / (rayDen n b : ℝ) := by
    rw [← scaled_rayY S _ _ hn', ← scaled_rayY S _ _ hn']
    push_cast
    exact mul_le_mul_of_nonneg_left (rayY_monotone (by positivity) (ord h) ((ord hb).trans last)) hS
  exact ⟨ediv_mono_frac (rayDen_pos _ hn') (rayDen_pos _ hn') (cm hlj),
    ceil_mono_frac (rayDen_pos _ hn') (rayDen_pos _ hn') (cm hik),
    ediv_mono_frac (rayDen_pos _ hn') (rayDen_pos _ hn') (sm hik (hkl.trans hlj)),
    ceil_mono_frac (rayDen_pos _ hn') (rayDen_pos _ hn') (sm hlj le_rfl)⟩

theorem weightedBin_zero_of_skipped (tree : Segments) (ok : tree.Valid)
    {n i j k : Nat} (hn : 0 < n) (hik : i ≤ k) (hkj : k+1 ≤ j) (hj : j ≤ n)
    (sk : skipped tree (halfAngleBox n i j)) : weightedBin tree n k = 0 := by
  obtain ⟨hxl,hxh,hyl,hyh⟩ := halfAngleBox_refines hn hik (Nat.le_succ k) hkj hj
  simp only [skipped,Bool.and_eq_true] at sk
  rcases sk with ⟨a,b⟩
  have sx : (halfAngleBox n i j).shiftX ≤ (halfAngleBox n k (k+1)).shiftX := by
    exact sub_le_sub_left hxh _
  have sy : (halfAngleBox n i j).shiftY ≤ (halfAngleBox n k (k+1)).shiftY := by
    exact max_le_max_left 0 (max_le_max (sub_le_sub_left hyh _) (sub_le_sub_right hyl _))
  have az := tree.area_eq_zero_of_misses ok a hxl hyl
  have bz := tree.area_eq_zero_of_misses ok b sx sy
  simp only [weightedBin,boxArea,tree.fastArea_eq ok,az,bz,Int.add_zero,Int.zero_mul]
  simp [ceilDiv]

end HadwigerNelson.Angular
