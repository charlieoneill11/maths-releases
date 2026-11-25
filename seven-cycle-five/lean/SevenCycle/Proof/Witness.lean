import SevenCycle.Proof.Model

namespace SevenCycle.Proof

private def far (a b : ZMod 7) : Bool :=
  let d := (a.val + 7 - b.val) % 7
  1 < d && d < 6

private theorem far_sound : ∀ a b : ZMod 7, far a b = true →
    a - b ∉ ({-1, 0, 1} : Finset (ZMod 7)) := by decide

/-- Every pair of different row indices has a separating coordinate. -/
def rowsCheck {n : ℕ} (rows : Array (Tuple n)) : Bool :=
  let indices := Array.finRange rows.size
  indices.all fun i => indices.all fun j => i == j ||
    (Array.finRange n).any fun k => far (rows[i] k) (rows[j] k)

/-- The image of a table of words as a mathematical code candidate. -/
def rowSet {n : ℕ} (rows : Array (Tuple n)) : Finset (Tuple n) :=
  Finset.univ.image (fun (i : Fin rows.size) => rows[i])

/-- A successful check proves both distinctness of all rows and the product-code property. -/
theorem rowsCheck_sound {n : ℕ} (rows : Array (Tuple n)) (ok : rowsCheck rows = true) :
    (rowSet rows).card = rows.size ∧ packing cycleStep (rowSet rows) := by
  have inRange {m : ℕ} (i : Fin m) : i ∈ Array.finRange m :=
    Array.mem_ofFn.mpr ⟨i, rfl⟩
  have sep (i j : Fin rows.size) (hne : i ≠ j) :
      ∃ k, rows[i] k - rows[j] k ∉ ({-1, 0, 1} : Finset (ZMod 7)) := by
    unfold rowsCheck at ok
    have oi := (Array.all_eq_true'.mp ok) i (inRange i)
    have oij := (Array.all_eq_true'.mp oi) j (inRange j)
    have hk := (Bool.or_eq_true_iff.mp oij).resolve_left (by simpa using hne)
    obtain ⟨k, _, h⟩ := Array.any_eq_true'.mp hk
    exact ⟨k, far_sound _ _ h⟩
  have hinj : Function.Injective (fun (i : Fin rows.size) => rows[i]) := by
    intro i j heq
    change rows[i] = rows[j] at heq
    by_contra h
    obtain ⟨k, hk⟩ := sep i j h
    rw [heq, sub_self] at hk
    exact hk (by simp)
  constructor
  · rw [rowSet, Finset.card_image_of_injective _ hinj]
    exact Finset.card_fin _
  · intro x hx y hy h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk⟩ := sep i j (fun hij => h.1 (congrArg (fun (t : Fin rows.size) => rows[t]) hij))
    exact hk (h.2 k)

end SevenCycle.Proof
