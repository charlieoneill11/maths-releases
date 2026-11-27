import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.NoncommRing

namespace Promislow

section
variable {R : Type*} [Ring R]

/-- Congruence in the local order O; the witness is an actual member of O. -/
def Near (O : Subring R) (f : R) (n : ℕ) (x : R) : Prop :=
  ∃ t ∈ O, x = 1 + f ^ n * t

private theorem value_mem {O : Subring R} {f x : R} {n : ℕ}
    (hf : f ∈ O) (h : Near O f n x) : x ∈ O := by
  obtain ⟨t, ht, rfl⟩ := h
  exact O.add_mem O.one_mem (O.mul_mem (O.pow_mem hf _) ht)

def commWord (x y : Rˣ) : Rˣ := x * y * x⁻¹ * y⁻¹

theorem near_comm {O : Subring R} {f : R} (cf : ∀ t, Commute f t)
    {x y : Rˣ} {i j : ℕ} (hx : Near O f i (x : R)) (hy : Near O f j (y : R))
    (hxi : (↑x⁻¹ : R) ∈ O) (hyi : (↑y⁻¹ : R) ∈ O) :
    Near O f (i+j) (commWord x y : R) := by
  obtain ⟨s, hs, ex⟩ := hx
  obtain ⟨t, ht, ey⟩ := hy
  refine ⟨(s*t-t*s) * ↑x⁻¹ * ↑y⁻¹,
    O.mul_mem (O.mul_mem (O.sub_mem (O.mul_mem hs ht) (O.mul_mem ht hs)) hxi) hyi, ?_⟩
  have xy : (x:R)*y - (y:R)*x = f^(i+j)*(s*t-t*s) := by
    rw [ex, ey, pow_add]
    have l : (f^i*s)*(f^j*t) = f^i*f^j*(s*t) := by
      simp only [mul_assoc, ((cf s).pow_left j).symm.left_comm]
    have r : (f^j*t)*(f^i*s) = f^i*f^j*(t*s) := by
      rw [((Commute.refl f).pow_pow i j).eq]
      simp only [mul_assoc, ((cf t).pow_left i).symm.left_comm]
    rw [mul_sub, ← l, ← r]
    noncomm_ring
  change (x:R)*y*↑x⁻¹*↑y⁻¹ = _
  calc
    _ = 1 + ((x:R)*y - (y:R)*x)*↑x⁻¹*↑y⁻¹ := by
      simp [sub_mul, mul_assoc]
    _ = _ := by rw [xy]; simp only [mul_assoc]

def deepWord (x y : Rˣ) : Rˣ := commWord (commWord (commWord x y) x) x

def NearUnit (O : Subring R) (f : R) (n : ℕ) (x : Rˣ) : Prop :=
  Near O f n (x:R) ∧ Near O f n (↑x⁻¹:R)

theorem nearUnit_comm {O : Subring R} {f : R} (hf : f ∈ O) (cf : ∀ t, Commute f t)
    {x y : Rˣ} {i j : ℕ} (hx : NearUnit O f i x) (hy : NearUnit O f j y) :
    NearUnit O f (i+j) (commWord x y) := by
  refine ⟨near_comm cf hx.1 hy.1 (value_mem hf hx.2) (value_mem hf hy.2), ?_⟩
  have rev := near_comm cf hy.1 hx.1 (value_mem hf hy.2) (value_mem hf hx.2)
  have eqn : (commWord x y)⁻¹ = commWord y x := by simp [commWord, mul_assoc]
  rw [eqn, Nat.add_comm]
  exact rev

theorem nearUnit_deep {O : Subring R} {f : R} (hf : f ∈ O) (cf : ∀ t, Commute f t)
    {x y : Rˣ} (hx : NearUnit O f 1 x) (hy : NearUnit O f 1 y) :
    NearUnit O f 4 (deepWord x y) :=
  nearUnit_comm hf cf (nearUnit_comm hf cf (nearUnit_comm hf cf hx hy) hx) hx

/-- Undo the four-atom change of basis, consuming the four powers just gained. -/
theorem unconjugate {O : Subring R} {f x : R} {c : Rˣ} (cf : ∀ t, Commute f t)
    (hc : (c:R) ∈ O) (hi : f^4*(↑c⁻¹:R) ∈ O)
    (h : Near O f 4 ((↑c⁻¹:R)*x*c)) : x ∈ O := by
  obtain ⟨t,ht,he⟩ := h
  have e := congrArg (fun a : R => (c:R)*a*(↑c⁻¹:R)) he
  simp [mul_assoc] at e
  rw [e, add_mul, one_mul, mul_add, Units.mul_inv]
  apply O.add_mem O.one_mem
  convert O.mul_mem (O.mul_mem hc ht) hi using 1
  simp only [mul_assoc, ((cf t).pow_left 4).left_comm]

end
end Promislow
