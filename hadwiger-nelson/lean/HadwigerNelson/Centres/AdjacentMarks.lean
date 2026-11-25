import HadwigerNelson.Crossings.ChordSide

namespace HadwigerNelson.Crossings
open Centres
noncomputable section

namespace CircleKnots

def prev {d} (i : Fin d) : Fin d :=
  if 0 < i.val then ⟨i.val-1,by have := i.isLt; omega⟩
  else ⟨d-1,by have := i.isLt; omega⟩

theorem prev_next {d} (i : Fin d) : prev (next i) = i := by
  apply Fin.ext
  unfold next
  split <;> simp only [prev,first] <;> split <;> simp_all <;> omega

theorem next_prev {d} (i : Fin d) : next (prev i) = i := by
  apply Fin.ext
  unfold prev
  split <;> simp only [next,first] <;> split <;> simp_all <;> omega

end CircleKnots
namespace CircleMarks
open CircleKnots

private theorem side_cyclic (p q r : Plane) : side p q r = side q r p := by unfold side; ring
private theorem side_reverse (p q r : Plane) : side p q r = -side p r q := by unfold side; ring

private theorem side_pos {X : Finset Plane} {c : Plane} {i j k : Fin (unitDegree X c)} (ij : i<j) (jk : j<k) :
    0 < side (mark X c i) (mark X c j) (mark X c k) := by
  rw [show side (mark X c i) (mark X c j) (mark X c k) = _ from
    circle_side c (knot X c i) (knot X c j) (knot X c k)]
  have s {u v : Fin (unitDegree X c)} (h : u<v) :
      0<Real.sin ((knot X c v-knot X c u)/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [(knot X c).strictMono h]) (by linarith [spread X c v u])
  exact mul_pos (mul_pos (mul_pos (by norm_num) (s ij)) (s jk)) (s (ij.trans jk))

private theorem adj_of_lt (X : Finset Plane) (c : Plane) {i j : Fin (unitDegree X c)} (ij : i<j)
    (h : consecutive X c (mark X c i) (mark X c j)) : j = next i ∨ i = next j := by
  by_cases hnext : i.val+1 = j.val
  · left
    have hi : i.val+1 < unitDegree X c := hnext ▸ j.isLt
    exact Fin.ext (by simp [next,hnext])
  right
  have iv : i.val<j.val := ij
  have ei : i.val+1<j.val := by omega
  let e : Fin (unitDegree X c) := ⟨i.val+1,by omega⟩
  have n : side (mark X c i) (mark X c j) (mark X c e) < 0 := by
    rw [side_reverse]
    exact neg_neg_of_pos (side_pos (show i<e from Nat.lt_succ_self _) (show e<j from ei))
  have hc (k : Fin (unitDegree X c)) : dist c (mark X c k) = 1 := by rw [dist_comm]; exact dist_circlePoint _ _
  have no (k : Fin (unitDegree X c)) : side (mark X c i) (mark X c j) (mark X c k) ≤ 0 := by
    rcases h.2.2.2 with all|all
    · exact False.elim (n.not_ge (all _ (mark X c e).property (hc e)))
    · exact all _ (mark X c k).property (hc k)
  have last : ¬j.val+1<unitDegree X c := by
    intro hj
    let f : Fin (unitDegree X c) := ⟨j.val+1,hj⟩
    exact (side_pos ij (show j<f from Nat.lt_succ_self _)).not_ge (no f)
  have first : i.val=0 := by
    by_contra nz
    let f := CircleKnots.first i
    have hfi : f < i := by change 0 < i.val; omega
    have pos := side_pos hfi ij
    rw [side_cyclic] at pos
    exact pos.not_ge (no f)
  apply Fin.ext
  simp [next,last,CircleKnots.first,first]

theorem consecutive_adjacent (X : Finset Plane) (c : Plane) (i j : Fin (unitDegree X c))
    (h : consecutive X c (mark X c i) (mark X c j)) : j = next i ∨ i = next j := by
  rcases lt_trichotomy i j with lt|eq|gt
  · exact adj_of_lt X c lt h
  · exact False.elim (h.1 (eq ▸ rfl))
  · exact (adj_of_lt X c gt (consecutive_comm.mp h)).symm

attribute [local instance] Classical.propDecidable

/-- On a marked circle the half-plane definition permits at most two neighbours of a mark. -/
theorem adjacent_count (X : Finset Plane) (c p : Plane) (hp : p ∈ X) :
    (X.filter fun q ↦ consecutive X c p q).card ≤ 2 := by
  classical
  by_cases any : ∃ i, (mark X c i:Plane) = p
  · obtain ⟨i,rfl⟩ := any
    let S : Finset Plane := {(mark X c (next i):Plane),(mark X c (prev i):Plane)}
    have sub : (X.filter fun q ↦ consecutive X c (mark X c i) q) ⊆ S := by
      intro q h
      obtain ⟨qX,near⟩ := Finset.mem_filter.mp h
      obtain ⟨j,rfl⟩ := mark_surj X c qX (by rw [dist_comm]; exact near.2.2.1)
      rcases consecutive_adjacent X c i j near with rfl|eq
      · simp [S]
      · have jprev : j=prev i := by rw [eq,prev_next]
        rw [jprev]; simp [S]
    exact (Finset.card_le_card sub).trans (Finset.card_le_two)
  · have empty : (X.filter fun q ↦ consecutive X c p q) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q h
        obtain ⟨_,yes⟩ := Finset.mem_filter.mp h
        exact any (mark_surj X c hp (by rw [dist_comm]; exact yes.2.1))
    simp [empty]

end CircleMarks
end
end HadwigerNelson.Crossings
