import HadwigerNelson.Stars.Partial.Intervals
import HadwigerNelson.Stars.StripGeometry

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Status)

noncomputable section

def InBand (j : Int) (x y : ℝ) : Prop :=
  j*500000000000 < y ∧ y < ((j:ℝ)+1)*500000000000 ∧
  scaled PartialWave.datum.left (y-j*500000000000) < x ∧
  x < scaled PartialWave.datum.right (y-j*500000000000)

private theorem local_range {j lo hi : Int} {y : ℝ} (ly : (lo:ℝ) ≤ y) (yh : y ≤ hi)
    (yl : (j:ℝ)*500000000000 ≤ y) (yr : y ≤ ((j:ℝ)+1)*500000000000) :
    let a := max 0 (lo-j*500000000000)
    let b := min 500000000000 (hi-j*500000000000)
    (a:ℝ) ≤ y-j*500000000000 ∧ y-j*500000000000 ≤ b := by
  push_cast
  exact ⟨max_le (by linarith) (by linarith),le_min (by linarith) (by linarith)⟩

theorem strip_sound (lo hi low high j : Int) (x y : ℝ) (xl : lo < x) (xr : x < hi)
    (yl : low < y) (yr : y < high) :
    (strip lo hi low high j = .inside → InBand j x y) ∧
    (strip lo hi low high j = .outside → ¬ InBand j x y) := by
  let a := max 0 (low-j*500000000000)
  let b := min 500000000000 (high-j*500000000000)
  let mid := a ≤ 250000000000 && 250000000000 ≤ b
  let lower := if mid then 0 else min (left a).1 (left b).1
  let upper := if mid then peak else max (right a).2 (right b).2
  let contained := ((max (left a).2 (left b).2 < lo ∧ hi < min (right a).1 (right b).1) ∧
    j*500000000000 < low) ∧ high < (j+1)*500000000000
  let possible := lower ≤ hi ∧ lo ≤ upper
  have defn : strip lo hi low high j =
      if b<a then .outside else if contained then .inside else
      if possible then .uncertain else .outside := by
    simp only [strip,a,b,mid,lower,upper,contained,possible,Bool.and_eq_true,decide_eq_true_eq]
    rfl
  rw [defn]
  have bound (yl' : (j:ℝ)*500000000000 ≤ y) (yr' : y ≤ ((j:ℝ)+1)*500000000000) :=
    local_range yl.le yr.le yl' yr'
  have za : 0 ≤ a := le_max_left ..
  have bh : b ≤ 500000000000 := min_le_left ..
  by_cases empty : b<a
  · simp only [if_pos empty,reduceCtorEq,false_implies,true_implies,true_and]
    rintro ⟨p,q,-,-⟩
    obtain ⟨aa,bb⟩ := bound p.le q.le
    exact (not_le_of_gt empty) (by exact_mod_cast aa.trans bb)
  rw [if_neg empty]
  by_cases inside : contained
  · simp only [if_pos inside,true_implies,reduceCtorEq,false_implies,and_true]
    obtain ⟨⟨⟨lx,rx⟩,py⟩,qy⟩ := inside
    have p : (j:ℝ)*500000000000 < y := (show (j:ℝ)*500000000000 < (low:ℝ) by exact_mod_cast py).trans yl
    have q : y < ((j:ℝ)+1)*500000000000 := yr.trans (by exact_mod_cast qy)
    have ⟨aa,bb⟩ := bound p.le q.le
    have walls := wall_bounds a b _ za bh aa bb
    exact ⟨p,q,walls.2.1.trans_lt ((Int.cast_lt (R:=ℝ)).mpr lx |>.trans xl),
      xr.trans (((Int.cast_lt (R:=ℝ)).mpr rx).trans_le walls.2.2.1)⟩
  rw [if_neg inside]
  by_cases existsPoint : possible
  · simp [existsPoint]
  simp only [if_neg existsPoint,reduceCtorEq,false_implies,true_implies,true_and]
  rintro ⟨p,q,w₀,w₁⟩
  obtain ⟨aa,bb⟩ := bound p.le q.le
  have walls := wall_bounds a b _ za bh aa bb
  apply existsPoint
  exact ⟨by exact_mod_cast (walls.1.trans (w₀.trans xr).le),by exact_mod_cast ((xl.trans w₁).le.trans walls.2.2.2)⟩

end
end HadwigerNelson.Stars.PartialCheck
