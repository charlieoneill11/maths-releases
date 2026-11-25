import HadwigerNelson.Angular.BlockSound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace HadwigerNelson.Angular
open Arithmetic

/-- The final integer ceiling accounts for the angular Jacobian on one bin. -/
theorem weightedBin_bound (tree : Segments) {n : Nat} (hn : 0 < n) (j : Nat) :
    (boxArea tree (halfAngleBox n j (j+1)) : ℝ)*n/((n:ℝ)*n+(j:ℝ)*j) ≤
      (weightedBin tree n j : ℝ) := by
  let a := boxArea tree (halfAngleBox n j (j+1))
  have den : (0:Int) < (n:Int)*n+(j:Int)*j := rayDen_pos j (by exact_mod_cast hn)
  have h := real_le_ceilDiv (a*n) den
  have g : ceilDiv (a*n) ((n:Int)*n+(j:Int)*j) ≤
      (weightedBin tree n j : Int) := Int.self_le_toNat _
  have g' : (ceilDiv (a*n) ((n:Int)*n+(j:Int)*j) : ℝ) ≤ (weightedBin tree n j : ℝ) := by
    exact_mod_cast g
  push_cast at h
  exact h.trans g'

/-- Summed real angular weights are bounded by the executable integer sum.
The first factor of two in the Jacobian cancels the checker’s twice-area units. -/
theorem angular_weight_bound (w : Array Nat) {n : Nat} (hn : 0<n) (hdiv : 4096 ∣ n) :
    (∑ j ∈ Finset.range n,
       (boxArea (tabulate w CompleteWave.step 11 0) (halfAngleBox n j (j+1)) : ℝ)*
         n/((n:ℝ)*n+(j:ℝ)*j)) ≤ (angularSum w n : ℝ) := by
  rw [angularSum_spec w hn hdiv,Nat.cast_sum]
  exact Finset.sum_le_sum (fun j _ => weightedBin_bound _ hn j)

end HadwigerNelson.Angular
