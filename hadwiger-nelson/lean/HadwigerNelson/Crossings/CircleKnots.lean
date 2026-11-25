import HadwigerNelson.Crossings.CircleParam

/-! Consecutive intervals in a cyclically ordered list of marks. The last
interval ends at the first mark plus one full turn. -/

namespace HadwigerNelson.Crossings
noncomputable section
namespace CircleKnots

variable {d : Nat}

def first (i : Fin d) : Fin d := ⟨0, by have := i.isLt; omega⟩

def next (i : Fin d) : Fin d :=
  if h : i.val+1<d then ⟨i.val+1,h⟩ else first i

def stop (t : Fin d → ℝ) (i : Fin d) : ℝ :=
  if i.val+1<d then t (next i) else t (next i)+2*Real.pi

theorem next_ne (h : 2 ≤ d) (i : Fin d) : next i ≠ i := by
  intro eq
  have v := congrArg Fin.val eq
  unfold next at v
  split at v <;> simp only [first] at v <;> omega

theorem next_next_ne (h : 3 ≤ d) (i : Fin d) : next (next i) ≠ i := by
  intro eq
  have v := congrArg Fin.val eq
  by_cases hi : i.val+1<d
  · simp only [next,hi,dif_pos] at v
    split at v <;> simp only [first] at v <;> omega
  · simp [next, first, hi, show 1 < d by omega] at v
    omega

variable (t : Fin d → ℝ) (ord : StrictMono t)
variable (spread : ∀ i j, t i-t j < 2*Real.pi)

include ord in
theorem base_le (i j : Fin d) : t (first i) ≤ t j :=
  ord.monotone (by change 0 ≤ j.val; omega)

include spread in
theorem mark_lt_period (i j : Fin d) : t j < t (first i)+2*Real.pi := by
  linarith [spread j (first i)]

include ord spread in
theorem start_lt_stop (i : Fin d) : t i < stop t i := by
  by_cases hi : i.val+1<d
  · simpa [stop,next,hi] using (ord (show i < (⟨i.val+1,hi⟩:Fin d) by exact Nat.lt_succ_self _))
  · simp only [stop,hi,if_false,next]
    exact mark_lt_period t spread i i

include spread in
theorem stop_le_period (i : Fin d) : stop t i ≤ t (first i)+2*Real.pi := by
  by_cases hi : i.val+1<d
  · exact (if_pos hi : stop t i = _).le.trans (mark_lt_period t spread i (next i)).le
  · simp [stop,hi,next]

include ord spread in
theorem short (h : 2 ≤ d) (i : Fin d) : stop t i-t i < 2*Real.pi := by
  by_cases hi : i.val+1<d
  · simpa [stop,hi] using spread (next i) i
  · have hfirst : first i < i := by change 0 < i.val; omega
    simpa [stop,next,hi] using (show t (first i)+2*Real.pi-t i < 2*Real.pi by linarith [ord hfirst])

include ord in
theorem stop_le_later {i j : Fin d} (h : i<j) : stop t i ≤ t j := by
  have h' : i.val < j.val := h
  have hi : i.val+1<d := by omega
  simp [stop,next,hi]
  exact ord.monotone (show (⟨i.val+1,hi⟩:Fin d) ≤ j from h')

include ord in
theorem not_inside (i j : Fin d) : t j ∉ Set.Ioo (t i) (stop t i) := by
  intro h
  have lt : i < j := lt_of_not_ge fun h' => (ord.monotone h').not_gt h.1
  exact (stop_le_later t ord lt).not_gt h.2

theorem stop_point (c : Plane) (i : Fin d) : circlePoint c (stop t i) = circlePoint c (t (next i)) := by
  by_cases hi : i.val+1<d <;> simp [stop,hi,circlePoint_add_period]

end CircleKnots
end
end HadwigerNelson.Crossings
