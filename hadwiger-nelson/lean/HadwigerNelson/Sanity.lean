import HadwigerNelson.Plane
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace HadwigerNelson.Sanity

private theorem unit_dist_of_coords {a b c d : ℝ}
    (h : (a - c) ^ 2 + (b - d) ^ 2 = 1) :
    dist (!₂[a, b] : Plane) !₂[c, d] = 1 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  change Real.sqrt (dist a c ^ 2 + dist b d ^ 2) = 1
  simp only [Real.dist_eq, sq_abs, h, Real.sqrt_one]

/-- The 3–4–5 displacement has Euclidean length one. -/
theorem dist_three_fifths_four_fifths :
    dist (!₂[0, 0] : Plane) !₂[3 / 5, 4 / 5] = 1 :=
  unit_dist_of_coords (by norm_num)

noncomputable def unitTriangle : Finset Plane := by
  classical
  exact {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

/-- All three sides of the displayed triangle have length one. -/
theorem unit_triangle_side_lengths :
    dist (!₂[0, 0] : Plane) !₂[1, 0] = 1 ∧
    dist (!₂[0, 0] : Plane) !₂[1 / 2, Real.sqrt 3 / 2] = 1 ∧
    dist (!₂[1, 0] : Plane) !₂[1 / 2, Real.sqrt 3 / 2] = 1 := by
  refine ⟨unit_dist_of_coords (by norm_num), unit_dist_of_coords ?_, unit_dist_of_coords ?_⟩ <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- The three vertices of this equilateral unit triangle require three different colours. -/
theorem unit_triangle_no_two_colouring :
    ¬ ∃ c : Plane → Fin 2,
      ∀ x ∈ unitTriangle, ∀ y ∈ unitTriangle, dist x y = 1 → c x ≠ c y := by
  classical
  rintro ⟨c, proper⟩
  obtain ⟨hab, had, hbd⟩ := unit_triangle_side_lengths
  have ab := proper _ (by simp [unitTriangle]) _ (by simp [unitTriangle]) hab
  have ad := proper _ (by simp [unitTriangle]) _ (by simp [unitTriangle]) had
  have bd := proper _ (by simp [unitTriangle]) _ (by simp [unitTriangle]) hbd
  have pigeonhole : ∀ i j k : Fin 2, i ≠ j → i ≠ k → j ≠ k → False := by decide
  exact pigeonhole _ _ _ ab ad bd

/-- A single unit edge is a counterexample to the one-colour form of the edge bound. -/
theorem edges_le_245510_one_colour_false :
    ¬ ∀ E : Finset (Plane × Plane), (∀ e ∈ E, dist e.1 e.2 = 1) →
      E.card ≤ 245510 → ∃ c : Plane → Fin 1, ∀ e ∈ E, c e.1 ≠ c e.2 := by
  classical
  intro all
  let e : Plane × Plane := (!₂[0, 0], !₂[3 / 5, 4 / 5])
  have unit : ∀ f ∈ ({e} : Finset (Plane × Plane)), dist f.1 f.2 = 1 := by
    intro f hf
    obtain rfl := Finset.mem_singleton.mp hf
    exact dist_three_fifths_four_fifths
  obtain ⟨c, proper⟩ := all {e} unit (by norm_num)
  exact proper e (by simp) (Subsingleton.elim _ _)

/-- Two points one unit apart contradict the one-colour form of the point bound. -/
theorem points_le_10689_one_colour_false :
    ¬ ∀ X : Finset Plane, X.card ≤ 10689 → ∃ c : Plane → Fin 1,
      ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y := by
  classical
  intro all
  let a : Plane := !₂[0, 0]
  let b : Plane := !₂[3 / 5, 4 / 5]
  have hcard : ({a, b} : Finset Plane).card ≤ 10689 :=
    (Finset.card_insert_le a {b}).trans (by norm_num)
  obtain ⟨c, proper⟩ := all {a, b} hcard
  exact proper a (by simp) b (by simp) dist_three_fifths_four_fifths (Subsingleton.elim _ _)

end HadwigerNelson.Sanity
