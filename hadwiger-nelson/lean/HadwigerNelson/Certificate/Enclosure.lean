import HadwigerNelson.Certificate.Objective

namespace HadwigerNelson.Certificate.ParameterBoxes

/-- Pair the two interpretations of the arithmetic, retaining their enclosure
as a proof. Projection erases the other interpretation at each operation. -/
structure Enclosed where
  bounds : Interval
  value : ℝ
  contains : bounds.Contains value

noncomputable instance : Operations Enclosed where
  constant q := ⟨Interval.point q, q, Interval.point_sound q⟩
  add a b := ⟨.add a.bounds b.bounds,a.value+b.value,Interval.add_sound a.contains b.contains⟩
  sub a b := ⟨.sub a.bounds b.bounds,a.value-b.value,Interval.sub_sound a.contains b.contains⟩
  mul a b := ⟨.mul a.bounds b.bounds,a.value*b.value,Interval.mul_sound a.contains b.contains⟩
  min a b := ⟨.minimum a.bounds b.bounds,min a.value b.value,Interval.min_sound a.contains b.contains⟩
  max a b := ⟨.maximum a.bounds b.bounds,max a.value b.value,Interval.max_sound a.contains b.contains⟩
  root a := ⟨.sqrt a.bounds,Real.sqrt a.value,Interval.sqrt_sound a.contains⟩
  intPart a := ⟨.floor a.bounds,(⌊a.value⌋ : ℤ),Interval.floor_sound a.contains⟩

theorem firstTerms_sound (m s j : Enclosed) :
    (firstTerms m.bounds s.bounds j.bounds (variance m.bounds)).Contains
    (firstTerms m.value s.value j.value (variance m.value)) :=
  (firstTerms m s j (variance m)).contains

theorem credit_sound (m s j h : Enclosed) (high low slope : ℚ) :
    (credit (budgets m.bounds s.bounds j.bounds h.bounds (variance m.bounds)) high low slope).Contains
    (credit (budgets m.value s.value j.value h.value (variance m.value)) high low slope) :=
  (credit (budgets m s j h (variance m)) high low slope).contains

theorem credit_nonneg (b : Budget ℝ) (hi lo sl : ℚ) : 0 ≤ credit b hi lo sl := by
  unfold credit
  exact (show (0:ℝ) ≤ (Operations.constant (0:ℚ):ℝ) by simp [Operations.constant]).trans (le_max_left _ _)

end HadwigerNelson.Certificate.ParameterBoxes
