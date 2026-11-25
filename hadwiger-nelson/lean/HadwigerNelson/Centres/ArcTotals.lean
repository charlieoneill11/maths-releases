import HadwigerNelson.Centres.ArcAngles
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin

namespace HadwigerNelson.Centres
open Finset Crossings CircleKnots
noncomputable section
attribute [local instance] Classical.propDecidable

def arcsOn (X Z : Finset Plane) : Finset (Arc X) := Finset.univ.filter fun e ↦ (head e:Plane)∈Z

@[simp] theorem mem_arcsOn {X Z : Finset Plane} {e : Arc X} : e∈arcsOn X Z ↔ (head e:Plane)∈Z := by
  simp [arcsOn]

@[simp] theorem arcsOn_self (X : Finset Plane) : arcsOn X X = univ := by
  ext e; simp [(head e).property]

theorem arcsOn_union (X Y Z : Finset Plane) : arcsOn X (Y∪Z) = arcsOn X Y ∪ arcsOn X Z := by ext; simp

theorem arcsOn_disjoint (X : Finset Plane) {Y Z : Finset Plane} (d : Disjoint Y Z) :
    Disjoint (arcsOn X Y) (arcsOn X Z) :=
  Finset.disjoint_left.mpr fun _ a b ↦ Finset.disjoint_left.mp d (mem_arcsOn.mp a) (mem_arcsOn.mp b)

theorem sum_arcsOn {M : Type*} [AddCommMonoid M] (X Z : Finset Plane) (f : Arc X → M) :
    ∑ e ∈ arcsOn X Z, f e = ∑ c : ↥X, if (c:Plane)∈Z then ∑ i, f ⟨c,i⟩ else 0 := by
  rw [arcsOn,Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro c _
  by_cases yes : (c:Plane)∈Z <;> simp [head,yes]

theorem sum_selected {M : Type*} [AddCommMonoid M] (X Z : Finset Plane) (sub : Z ⊆ X) (f : Plane → M) :
    (∑ c : ↥X, if (c:Plane)∈Z then f c else 0) = ∑ c ∈ Z, f c := by
  change (∑ c ∈ X.attach, if (c:Plane)∈Z then f c else 0) = _
  rw [Finset.sum_attach X (fun c ↦ if c∈Z then f c else 0),←Finset.sum_filter]
  congr 1
  ext c; simp only [mem_filter,and_iff_right_iff_imp]; exact fun h ↦ sub h

theorem card_arcsOn (X Z : Finset Plane) (sub : Z ⊆ X) :
    (arcsOn X Z).card = ∑ c ∈ Z, unitDegree X c := by
  rw [Finset.card_eq_sum_ones,sum_arcsOn]
  simpa using sum_selected X Z sub (unitDegree X)

theorem card_all_arcs (X : Finset Plane) : (univ : Finset (Arc X)).card = 2*unitEdgeCount X := by
  rw [← arcsOn_self,card_arcsOn _ _ (fun _ h ↦ h),sum_unitDegree]

theorem total_circle_angle {X : Finset Plane} (c : ↥X) : ∑ i, length (X:=X) ⟨c,i⟩ ≤ 2*Real.pi := by
  let d := unitDegree X c
  by_cases pos : 0<d
  · let t := CircleMarks.knot X c
    let first : Fin d := ⟨0,pos⟩
    let s (i : ℕ) := if h : i<d then t ⟨i,h⟩ else t first+2*Real.pi
    have eq (i : Fin d) : length (X:=X) ⟨c,i⟩ = s (i.val+1)-s i.val := by
      change stop t i-t i = _
      by_cases hi : i.val+1<d
      · simp [s,stop,next,hi,show i.val+1<unitDegree X c from hi,i.isLt]
      · simp [s,stop,next,CircleKnots.first,first,hi,show ¬i.val+1<unitDegree X c from hi,i.isLt]
    simp_rw [eq]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ s (i+1)-s i),Finset.sum_range_sub]
    simp [s,pos,first,show ¬unitDegree X c < d from lt_irrefl _,add_comm]
  · have empty : IsEmpty (Fin (unitDegree X c)) := ⟨fun i ↦ pos (Nat.zero_lt_of_lt i.isLt)⟩
    simpa using Real.pi_pos.le

theorem angle_arcsOn (X Z : Finset Plane) (sub : Z ⊆ X) :
    ∑ e ∈ arcsOn X Z, length e ≤ 2*Real.pi*Z.card := by
  rw [sum_arcsOn]
  have h (c : ↥X) : (if (c:Plane)∈Z then ∑ i, length (X:=X) ⟨c,i⟩ else 0) ≤
      (if (c:Plane)∈Z then 2*Real.pi else 0) := by split <;> simp_all [total_circle_angle]
  have le := Finset.sum_le_sum (s:=Finset.univ) (fun c _ ↦ h c)
  rw [sum_selected X Z sub (fun _ ↦ 2*Real.pi)] at le
  simpa [mul_comm] using le

end
end HadwigerNelson.Centres
