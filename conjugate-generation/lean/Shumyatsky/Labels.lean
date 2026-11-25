import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

namespace Shumyatsky

/-- The permutation and the source-indexed labels of a factor action. -/
structure Labelled (ι A : Type*) where
  perm : Equiv.Perm ι
  label : ι → A

namespace Labelled

variable {ι A : Type*} [Group A]

def comp (u v : Labelled ι A) : Labelled ι A :=
  ⟨v.perm.trans u.perm, fun i => u.label (v.perm i) * v.label i⟩

theorem intertwines {x g y : Labelled ι A}
    (p : ∀ i, g.perm (x.perm i) = y.perm (g.perm i)) :
    comp g x = comp y g ↔
      ∀ i, g.label (x.perm i) = y.label (g.perm i) * g.label i * (x.label i)⁻¹ := by
  constructor
  · intro h i
    have e := congrArg (fun z : Labelled ι A => z.label i) h
    exact (eq_mul_inv_iff_mul_eq).2 e
  · intro h
    have hp : x.perm.trans g.perm = g.perm.trans y.perm := Equiv.ext p
    unfold comp
    congr 1
    funext i
    exact (eq_mul_inv_iff_mul_eq).1 (h i)

end Labelled

namespace Cycle

variable {A O : Type*} [Group A] [Group O]

/-- At each successive vertex the conjugator is forced by the x- and y-labels. -/
def transport (g : A) : List (A × A) → A
  | [] => g
  | (x, y) :: rest => transport (y * g * x⁻¹) rest

/-- Products of labels act with the first edge on the right. -/
def total (p : A × A → A) (edges : List (A × A)) := (edges.reverse.map p).prod

theorem transport_eq (g : A) (edges : List (A × A)) :
    transport g edges = total Prod.snd edges * g * (total Prod.fst edges)⁻¹ := by
  induction edges generalizing g with
  | nil => simp [transport, total]
  | cons a l ih =>
    rcases a with ⟨x,y⟩
    rw [transport, ih]
    simp [total, mul_assoc]

theorem closure_iff (g : A) (edges : List (A × A)) :
    transport g edges = g ↔ total Prod.snd edges = g * total Prod.fst edges * g⁻¹ := by
  rw [transport_eq]
  constructor <;> intro h
  · calc
      _ = (total Prod.snd edges * g * (total Prod.fst edges)⁻¹) * total Prod.fst edges * g⁻¹ := by group
      _ = _ := by rw [h]
  · rw [h]
    group

/-- Projecting every intermediate conjugator to the outer group commutes
with reconstruction, including at prefixes of a cycle. -/
theorem project_transport (q : A →* O) (g : A) (edges : List (A × A)) :
    q (transport g edges) = transport (q g) (edges.map fun e => (q e.1, q e.2)) := by
  induction edges generalizing g with
  | nil => rfl
  | cons a l ih =>
    rcases a with ⟨x,y⟩
    simp [transport, ih]

/-- Solve the closing equation with the reserved edge in any position.
Equality under q specifies the prescribed outer coset. -/
theorem reserved_label (q : A →* O) (left right target original : A)
    (outer : q (left * original * right) = q target) :
    ∃! z : A, left * z * right = target ∧ q z = q original := by
  refine ⟨left⁻¹ * target * right⁻¹, ⟨by group, ?_⟩, ?_⟩
  · simp only [map_mul, map_inv] at outer ⊢
    rw [← outer]
    group
  · rintro z ⟨h, _⟩
    rw [← h]
    group

/-- The two walks cross distinct free edges. Fixed tree paths multiply
each label on the left and right, giving independent full cosets. -/
theorem two_walks (q : A →* O) (l₁ r₁ z₁ l₂ r₂ z₂ w₁ w₂ : A)
    (h₁ : q w₁ = q (l₁ * z₁ * r₁)) (h₂ : q w₂ = q (l₂ * z₂ * r₂)) :
    ∃ a b, q a = q z₁ ∧ q b = q z₂ ∧ l₁ * a * r₁ = w₁ ∧ l₂ * b * r₂ = w₂ := by
  obtain ⟨a, ⟨ha, hqa⟩, _⟩ := reserved_label q l₁ r₁ w₁ z₁ h₁.symm
  obtain ⟨b, ⟨hb, hqb⟩, _⟩ := reserved_label q l₂ r₂ w₂ z₂ h₂.symm
  exact ⟨a, b, hqa, hqb, ha, hb⟩

end Cycle
end Shumyatsky
