import LeastPrime.Checker.Grid
import LeastPrime.Checker.Quadrature

/-! Integral bounds on finite partitions of the unit grid. -/

namespace LeastPrime.Checker

open MeasureTheory Set

noncomputable section

def area (n : Nat) : ℝ := (n : ℝ) / (unit : ℝ) ^ 2

theorem area_add (x y : Nat) : area (x + y) = area x + area y := by simp [area, add_div]

@[simp] theorem area_zero : area 0 = 0 := by simp [area]

theorem area_mul (x y : Nat) : area (x * y) = grid x * grid y := by
  simp only [area, grid, Nat.cast_mul, pow_two, div_mul_div_comm]

def Bounds (bound : Bound) (computed exact : ℝ) : Prop :=
  match bound with
  | .lower => computed ≤ exact
  | .upper => exact ≤ computed

theorem Bounds.refl (bound : Bound) (x : ℝ) : Bounds bound x x := by
  cases bound <;> exact le_rfl

theorem Bounds.add {bound : Bound} {a b c d : ℝ}
    (hab : Bounds bound a b) (hcd : Bounds bound c d) : Bounds bound (a + c) (b + d) := by
  cases bound <;> exact add_le_add hab hcd

theorem Bounds.trans {bound : Bound} {a b c : ℝ}
    (hab : Bounds bound a b) (hbc : Bounds bound b c) : Bounds bound a c := by
  cases bound
  · exact le_trans hab hbc
  · exact le_trans hbc hab

theorem Bounds.mul_nonneg_left {bound : Bound} {a b c : ℝ}
    (hab : Bounds bound a b) (hc : 0 ≤ c) : Bounds bound (c * a) (c * b) := by
  cases bound <;> exact mul_le_mul_of_nonneg_left hab hc

theorem final_rounding (bound : Bound) (n : Nat) :
    Bounds bound (grid (quotient bound n unit)) (area n) := by
  have h : ((n : ℝ) / (unit : ℝ)) / (unit : ℝ) = area n := by rw [area, div_div, pow_two]
  rw [← h]
  cases bound
  · exact div_le_div_of_nonneg_right (quotient_lower_le n unit) unit_real_pos.le
  · exact div_le_div_of_nonneg_right (le_quotient_upper (n := n) unit_pos) unit_real_pos.le

theorem integral_grid_self (f : ℝ → ℝ) (a : Nat) :
    (∫ r in Icc (grid a) (grid a), f r) = 0 := by
  rw [integral_Icc_eq_integral_Ioo, Ioo_self, setIntegral_empty]

theorem integral_grid_add {f : ℝ → ℝ} {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntegrableOn f (Icc (grid a) (grid c))) :
    (∫ r in Icc (grid a) (grid b), f r) + (∫ r in Icc (grid b) (grid c), f r) =
      ∫ r in Icc (grid a) (grid c), f r := by
  have hab' := grid_le_iff.mpr hab
  have hbc' := grid_le_iff.mpr hbc
  have h₁ := hf.mono_set (Icc_subset_Icc le_rfl hbc')
  have h₂ := hf.mono_set (Icc_subset_Icc hab' le_rfl)
  have hi₁ := (intervalIntegrable_iff_integrableOn_Icc_of_le hab').mpr h₁
  have hi₂ := (intervalIntegrable_iff_integrableOn_Icc_of_le hbc').mpr h₂
  simpa only [intervalIntegral.integral_of_le hab', intervalIntegral.integral_of_le hbc',
    intervalIntegral.integral_of_le (hab'.trans hbc'), ← integral_Icc_eq_integral_Ioc] using
    intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂

theorem integral_grid_const {a b : Nat} (hab : a ≤ b) (x : ℝ) :
    (∫ _ in Icc (grid a) (grid b), x) = (grid b - grid a) * x := by
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (grid_le_iff.mpr hab)]

theorem integral_grid_congr {f g : ℝ → ℝ} {a b : Nat}
    (h : EqOn f g (Ioo (grid a) (grid b))) :
    (∫ r in Icc (grid a) (grid b), f r) = ∫ r in Icc (grid a) (grid b), g r := by
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

theorem constant_cell_bounds (bound : Bound) {f : ℝ → ℝ} {a b val : Nat}
    (hab : a ≤ b) (hf : IntegrableOn f (Icc (grid a) (grid b)))
    (h : ∀ r ∈ Ioo (grid a) (grid b), Bounds bound (grid val) (f r)) :
    Bounds bound (area ((b - a) * val)) (∫ r in Icc (grid a) (grid b), f r) := by
  rw [area_mul, grid_sub hab, ← integral_grid_const hab, integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioo]
  have hf' := hf.mono_set Ioo_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => grid val) (Ioo (grid a) (grid b)) :=
    integrableOn_const measure_Ioo_lt_top.ne
  cases bound
  · exact setIntegral_mono_on hc hf' measurableSet_Ioo h
  · exact setIntegral_mono_on hf' hc measurableSet_Ioo h

/-- Sum the rounded cell contributions and compare with the full integral. -/
theorem sumGridCells_correct (bound : Bound) (f : ℝ → ℝ) (cell : Nat → Nat → Nat)
    (step a b : Nat) (hab : a ≤ b) (hf : IntegrableOn f (Icc (grid a) (grid b)))
    (hCell : ∀ x y, a ≤ x → x < y → y ≤ b →
      Bounds bound (area (cell x y)) (∫ r in Icc (grid x) (grid y), f r)) :
    Bounds bound (area (sumGridCells cell step a b)) (∫ r in Icc (grid a) (grid b), f r) := by
  by_cases h : a < b
  · let c := min (a + (step + 1)) b
    have hac : a < c := by dsimp [c]; omega
    have hcb : c ≤ b := min_le_right _ _
    have hf' : IntegrableOn f (Icc (grid c) (grid b)) :=
      hf.mono_set (Icc_subset_Icc (grid_le_iff.mpr hac.le) le_rfl)
    have hnext := sumGridCells_correct bound f cell step c b hcb hf'
      (fun x y hcx hxy hyb => hCell x y (hac.le.trans hcx) hxy hyb)
    rw [sumGridCells, dif_pos h]
    change Bounds bound (area (cell a c + sumGridCells cell step c b)) _
    rw [area_add, ← integral_grid_add hac.le hcb hf]
    exact (hCell a c le_rfl hac hcb).add hnext
  · have eq : a = b := le_antisymm hab (le_of_not_gt h)
    subst b
    rw [sumGridCells, dif_neg (Nat.lt_irrefl _), area_zero, integral_grid_self]
    exact Bounds.refl _ _
termination_by b - a
decreasing_by omega

/-- Adjacent entries of a grid subdivision. -/
inductive Adjacent (a b : Nat) : List Nat → Prop
  | head (rest) : Adjacent a b (a :: b :: rest)
  | tail (x) {rest} : Adjacent a b rest → Adjacent a b (x :: rest)

theorem Adjacent.left_mem {a b : Nat} {cuts : List Nat} (h : Adjacent a b cuts) : a ∈ cuts := by
  induction h with
  | head => simp
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem Adjacent.right_mem {a b : Nat} {cuts : List Nat} (h : Adjacent a b cuts) : b ∈ cuts := by
  induction h with
  | head => simp
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem Adjacent.no_interior {a b c : Nat} {cuts : List Nat} (h : Adjacent a b cuts)
    (hchain : cuts.Pairwise (· ≤ ·)) (hc : c ∈ cuts) : ¬ (a < c ∧ c < b) := by
  induction h with
  | head rest =>
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    have hbc := (List.pairwise_cons.mp hchain.tail).1 c hc
    omega
  | tail x hadj ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · have hxa := (List.pairwise_cons.mp hchain).1 a hadj.left_mem
      omega
    · exact ih hchain.tail hc

/-- Sum the quadrature estimates over an explicit list of cuts. -/
theorem sumCutCells_correct (bound : Bound) (g : Nat → Nat) (f : ℝ → ℝ)
    {a : Nat} {rest : List Nat}
    (hchain : (a :: rest).Pairwise (· ≤ ·))
    (hf : IntegrableOn f (Icc (grid a) (grid (rest.getLastD a))))
    (hCell : ∀ x y, Adjacent x y (a :: rest) → x ≤ y →
      Bounds bound (area ((y - x) * estimatedProbability bound x y (g x) (g y)))
        (∫ r in Icc (grid x) (grid y), f r)) :
    Bounds bound (area (sumCutCells bound g a (g a) rest))
      (∫ r in Icc (grid a) (grid (rest.getLastD a)), f r) := by
  induction rest generalizing a with
  | nil =>
    rw [List.getLastD_nil, sumCutCells, area_zero, integral_grid_self]
    exact Bounds.refl _ _
  | cons b rest ih =>
    have hab := (List.pairwise_cons.mp hchain).1 b List.mem_cons_self
    have hlast : (b :: rest).getLastD a = rest.getLastD b := List.getLastD_cons
    rw [hlast] at hf ⊢
    have hbc : b ≤ rest.getLastD b := by
      rcases List.mem_cons.mp (List.getLastD_mem_cons (l := rest) (a := b)) with h | h
      · omega
      · exact (List.pairwise_cons.mp hchain.tail).1 _ h
    have hfr : IntegrableOn f (Icc (grid b) (grid (rest.getLastD b))) :=
      hf.mono_set (Icc_subset_Icc (grid_le_iff.mpr hab) le_rfl)
    simp only [sumCutCells, area_add]
    rw [← integral_grid_add hab hbc hf]
    exact (hCell a b (.head rest) hab).add
      (ih hchain.tail hfr (fun x y hxy hle => hCell x y (.tail a hxy) hle))

end

end LeastPrime.Checker
