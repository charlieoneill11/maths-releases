import HadwigerNelson.Forest.BlankPairs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Charge each remaining unordered pair to an endpoint outside the inner layer.
This gives the three packing estimates in Lemma 42. -/

namespace HadwigerNelson.Forest
open scoped BigOperators
open Centres Packing
noncomputable section
attribute [local instance] Classical.propDecidable

theorem pair_degree_bounds (R D : Finset Plane) (t : ℝ) (K : ℕ)
    (sub : D⊆R) (bound : ∀ i∈R,nearDegree R i t ≤ K) :
    2*neighbourPairs R D t ≤ R.card*K ∧ neighbourPairs R D t ≤ (R.card-D.card)*K := by
  classical
  let N (x y : Plane) : Prop := x≠y ∧ dist x y ≤ 2*t
  let edge (x y : Plane) := if N x y then 1 else 0
  let out (x y : Plane) := if x∉D then edge x y else 0
  let kept (x y : Plane) := if x≠y ∧ ¬(x∈D ∧ y∈D) ∧ dist x y ≤ 2*t then 1 else 0
  have sym (x y) : edge x y=edge y x := by simp [edge,N,ne_comm,dist_comm]
  have degree (x) : (∑ y∈R,edge x y)=nearDegree R x t := by
    simp only [edge,N,nearDegree,Finset.sum_boole,Nat.cast_id]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro y _
    rw [dist_comm x y]
    exact and_congr_left' ne_comm
  have kept_le (x y) : kept x y ≤ edge x y := by
    simp only [kept,edge,N]
    split
    next h => rw [if_pos ⟨h.1,h.2.2⟩]
    next => exact Nat.zero_le _
  have pay (x y) : kept x y ≤ out x y + out y x := by
    by_cases keep : x≠y ∧ ¬(x∈D ∧ y∈D) ∧ dist x y≤2*t
    · have e : edge x y=1 := if_pos ⟨keep.1,keep.2.2⟩
      by_cases inD : x∈D
      · have notD : y∉D := fun h => keep.2.1 ⟨inD,h⟩
        simp [kept,keep,out,inD,notD,← sym x y,e]
      · have o : out x y=1 := by simp [out,inD,e]
        rw [show kept x y=1 from if_pos keep,o]
        omega
    · rw [show kept x y=0 from if_neg keep]
      exact Nat.zero_le _
  have twice : 2*neighbourPairs R D t ≤ ∑ x∈R,∑ y∈R,kept x y := by
    simp only [kept,Finset.sum_boole,neighbourPairs,Nat.cast_id]
    exact Nat.mul_div_le ..
  have all : (∑ x∈R,∑ y∈R,edge x y) ≤ R.card*K := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s:=R)
      (fun x hx => (degree x).trans_le (bound x hx))
  have excluded : (∑ x∈R,∑ y∈R,out x y) ≤ (R.card-D.card)*K := by
    have h (x) : (∑ y∈R,out x y)=if x∉D then nearDegree R x t else 0 := by
      by_cases b : x∈D <;> simp [out,b,degree]
    have sum := Finset.sum_le_sum (s:=R\D) (fun x hx => bound x (Finset.mem_sdiff.mp hx).1)
    rw [Finset.sum_const,nsmul_eq_mul,Finset.card_sdiff_of_subset sub] at sum
    simp_rw [h,← Finset.sum_filter]
    simpa [Finset.filter_notMem_eq_sdiff] using sum
  have twoCharges := Finset.sum_le_sum (s:=R) (fun x _ => Finset.sum_le_sum (s:=R) (fun y _ => pay x y))
  simp_rw [Finset.sum_add_distrib] at twoCharges
  rw [Finset.sum_comm (s:=R) (t:=R) (f:=fun x y => out y x)] at twoCharges
  exact ⟨twice.trans ((Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => kept_le x y))).trans all),
    by omega⟩

private theorem weighted_bounds {ι : Type*} (S : Finset ι) (pred : ι → Prop) [DecidablePred pred]
    (K N h : ι → ℝ) (r j factor : ℝ) (pos : 0≤factor) (hn : ∀ i∈S,0≤h i)
    (bnd : ∀ i∈S, 2*N i≤r*K i ∧ N i≤j*K i) :
    2*factor*(∑ i∈S,h i*N i) ≤ min (r*(factor*∑ i∈S,K i*h i))
      (min (r*(factor*∑ i∈S,if pred i then K i*h i else 0) +
        j*(2*(factor*∑ i∈S,if pred i then 0 else K i*h i)))
        (j*(2*(factor*∑ i∈S,K i*h i)))) := by
  have each (i) (hi : i∈S) : factor*(h i*(2*N i))≤factor*(h i*(r*K i)) ∧
      factor*(h i*(2*N i))≤factor*(h i*(2*(j*K i))) := by
    obtain ⟨a,b⟩ := bnd i hi
    exact ⟨mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a (hn i hi)) pos,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (hn i hi)) pos⟩
  simp only [Finset.mul_sum]
  apply le_min
  · apply Finset.sum_le_sum; intro i hi; linarith only [(each i hi).1]
  · apply le_min
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      by_cases p : pred i <;> simp only [p,ite_true,ite_false,mul_zero,add_zero,zero_add]
      · linarith only [(each i hi).1]
      · linarith only [(each i hi).2]
    · apply Finset.sum_le_sum; intro i hi; linarith only [(each i hi).2]

attribute [local irreducible] unitStep neighbourCap neighbourPairs

theorem collision_of_degree_cap {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {X : Finset Plane} (L : Layers X)
    (pointwise : ∀ k : Fin 16384, ∀ u∈L.R,
      nearDegree L.R u (unitBin (k.val+1)) ≤ neighbourCap a (unitBin (k.val+1))) :
    let K := packingSum Ω (fun _ => True)
    let T := packingSum Ω (fun t => d < t)
    let U := 2*packingSum Ω (fun t => t ≤ d)
    let j := L.R.card-L.D.card
    2*unitBin 1 / Real.pi * (∑ k : Fin 16384,unitStep Ω (k.val+1)*neighbourPairs L.R L.D (unitBin (k.val+1))) ≤
      min (L.R.card*K) (min (L.R.card*T + j*U) (j*(2*K))) := by
  let t (k : Fin 16384) := unitBin (k.val+1)
  let K (k : Fin 16384) : ℝ := neighbourCap a (t k)
  let N (k : Fin 16384) : ℝ := neighbourPairs L.R L.D (t k)
  let h (k : Fin 16384) := unitStep Ω (k.val+1)
  have bounds (k : Fin 16384) : 2*N k≤L.R.card*K k ∧ N k≤(L.R.card-L.D.card : ℕ)*K k := by
    obtain ⟨p,q⟩ := pair_degree_bounds L.R L.D (t k) _ L.maximalD.1 (pointwise k)
    dsimp only [N,K]
    exact ⟨by exact_mod_cast p,by exact_mod_cast q⟩
  have total := weighted_bounds Finset.univ (fun k => d<t k) K N h L.R.card (L.R.card-L.D.card : ℕ)
    (unitBin 1/Real.pi) (by unfold unitBin w; positivity)
    (fun k _ => unitStep_nonneg sound _) (fun k _ => bounds k)
  have partition (k : Fin 16384) :
      (if d<t k then (0:ℝ) else K k*h k)=(if t k ≤ d then K k*h k else 0) := by
    by_cases hy : d<t k <;> simp [hy,le_of_not_gt,not_le_of_gt]
  have eqf : (fun k : Fin 16384 => if d<t k then (0:ℝ) else K k*h k) =
      (fun k => if t k ≤ d then K k*h k else 0) := funext partition
  rw [eqf] at total
  dsimp only [packingSum]
  rw [mul_div_assoc 2]
  simp only [if_pos True.intro]
  convert total using 7

end
end HadwigerNelson.Forest
