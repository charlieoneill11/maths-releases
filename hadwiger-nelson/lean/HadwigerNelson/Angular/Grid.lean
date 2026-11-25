import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Floor.Semiring

namespace HadwigerNelson.Angular.Grid

/-- Piecewise affine interpolation on integer grid indices. The two outside
rays only serve to give the finite-interval profile a total domain. -/
noncomputable def interpolation (v : Nat → ℝ) : Nat → ℝ → ℝ
  | 0, _ => v 0
  | n+1, y => if y ≤ n then interpolation v n y else v n + (v (n+1)-v n)*(y-n)

theorem interpolation_right (v : Nat → ℝ) (n : Nat) :
    interpolation v n n = v n := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [interpolation,Nat.cast_succ]
    rw [if_neg (by linarith : ¬(k:ℝ)+1 ≤ k)]
    ring

theorem interpolation_on (v : Nat → ℝ) {i n : Nat} (hin : i < n)
    {y : ℝ} (hy : y ∈ Set.Icc (i:ℝ) ((i:ℝ)+1)) :
    interpolation v n y = v i + (v (i+1)-v i)*(y-i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [interpolation]
    by_cases h : i = n
    · subst i
      split_ifs with le
      · have eq : y = n := le_antisymm le hy.1
        rw [eq,interpolation_right]
        ring
      · rfl
    · have hlt : i < n := by omega
      have hle : (i:ℝ)+1 ≤ n := by exact_mod_cast (show i+1 ≤ n by omega)
      rw [if_pos (hy.2.trans hle)]
      exact ih hlt

theorem interpolation_continuous (v : Nat → ℝ) (n : Nat) : Continuous (interpolation v n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun y : ℝ => if y ≤ n then interpolation v n y
      else v n+(v (n+1)-v n)*(y-n))
    apply Continuous.if_le ih (by fun_prop) continuous_id continuous_const
    intro z hz
    change z = n at hz
    subst z
    rw [interpolation_right]
    ring

/-- Every point of a closed grid interval belongs to a cell, including the far endpoint. -/
theorem hasCell {n : Nat} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc 0 (n:ℝ)) :
    ∃ i : Nat, i < n ∧ u ∈ Set.Icc (i:ℝ) ((i:ℝ)+1) := by
  by_cases eq : u = (n:ℝ)
  · refine ⟨n-1,by omega,?_⟩
    rw [eq,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    constructor <;> linarith
  · have lt : u < (n:ℝ) := lt_of_le_of_ne hu.2 eq
    refine ⟨⌊u⌋₊,?_,Nat.floor_le hu.1,(Nat.lt_floor_add_one u).le⟩
    have h := (Nat.floor_le hu.1).trans_lt lt
    exact_mod_cast h

theorem reflect (v : Nat → ℝ) (n : Nat) (hn : 0<n) (sym : ∀ i ≤ n, v (n-i)=v i)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (n:ℝ)) :
    interpolation v n (n-u) = interpolation v n u := by
  obtain ⟨i,hi,lo,up⟩ := hasCell hn hu
  let j := n-(i+1)
  have hj : j < n := by dsimp [j]; omega
  have jc : (j:ℝ) = n-(i+1) := by dsimp [j]; rw [Nat.cast_sub (by omega)]; norm_num
  have jnext : j+1 = n-i := by dsimp [j]; omega
  have hy : n-u ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) := by rw [jc]; constructor <;> linarith
  rw [interpolation_on v hj hy,interpolation_on v hi ⟨lo,up⟩,jc]
  have lj : v j = v (i+1) := sym (i+1) (by omega)
  rw [lj,jnext,sym i hi.le]
  ring

theorem complement (v : Nat → ℝ) (m : Nat) (c : ℝ) (hm : 0<m)
    (sym : ∀ i ≤ m, v i+v (i+m)=c) {u : ℝ} (hu : u ∈ Set.Icc 0 (m:ℝ)) :
    interpolation v (2*m) u + interpolation v (2*m) (u+m) = c := by
  obtain ⟨i,hi,lo,up⟩ := hasCell hm hu
  have u1 : u ∈ Set.Icc (i:ℝ) ((i:ℝ)+1) := ⟨lo,up⟩
  have u2 : u+m ∈ Set.Icc ((i+m:Nat):ℝ) (((i+m:Nat):ℝ)+1) := by
    rw [Nat.cast_add]
    constructor <;> linarith
  rw [interpolation_on v (show i<2*m by omega) u1,
    interpolation_on v (show i+m<2*m by omega) u2,Nat.cast_add]
  have e : i+m+1 = (i+1)+m := by omega
  rw [e]
  have a := sym i hi.le
  have b := sym (i+1) (by omega)
  have aa : v (i+m)=c-v i := by linarith
  have bb : v ((i+1)+m)=c-v (i+1) := by linarith
  rw [aa,bb]
  ring

theorem between (v : Nat → ℝ) {n : Nat} (hn : 0<n) {a b : ℝ}
    (bounds : ∀ i ≤ n, a < v i ∧ v i < b) {u : ℝ} (hu : u ∈ Set.Icc 0 (n:ℝ)) :
    a < interpolation v n u ∧ interpolation v n u < b := by
  obtain ⟨i,hi,lo,up⟩ := hasCell hn hu
  rw [interpolation_on v hi ⟨lo,up⟩]
  obtain ⟨la,ra⟩ := bounds i hi.le
  obtain ⟨lb,rb⟩ := bounds (i+1) (by omega)
  by_cases vs : v i ≤ v (i+1)
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr vs) (sub_nonneg.mpr lo)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr vs) (sub_nonneg.mpr up)]
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge vs)) (sub_nonneg.mpr up)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge vs)) (sub_nonneg.mpr lo)]

end HadwigerNelson.Angular.Grid
