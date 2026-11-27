import Promislow.Slices

namespace Promislow
noncomputable section
open MonoidAlgebra

def signAt (a : Axis) (c : Coset) : ℤ :=
  match a with | .x => c.signX | .y => c.signY

theorem tr_slide (a : Axis) (n : ℤ) (g : ElemP) :
    g * tr a n = tr a (signAt a g.c * n) * g := by
  obtain ⟨x,y,z,c⟩ := g
  cases a <;> cases c <;>
    simp [tr,signAt,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
      ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ] <;> omega

theorem single_slide (g : ElemP) (r : ℤ) (a : Axis) (n : ℤ) :
    (single g r : IntegralGroupRing) * shift a n = shift a (signAt a g.c*n)*single g r := by
  simp [shift,single_mul_single,tr_slide]

private theorem f_form (l : Letter) : F l =
    match l with
    | .A => shift .x (-1) + (shift .x 0 + shift .x 1)
    | .A' => shift .x (-2) + (shift .x (-1) + (shift .x 0 + (shift .x 1 + shift .x 2)))
    | .B => shift .y (-1) + (shift .y 0 + shift .y 1) := by
  cases l <;> simp [F,Sparse.factor,Sparse.series,Letter.axis,Letter.degree,
    List.range_succ,Sparse.val,shift]

theorem centralF (l : Letter) (r : IntegralGroupRing) : Commute (F l) r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => exact Commute.zero_right _
  | add p q hp hq => exact hp.add_right hq
  | single g c =>
    change F l * single g c = single g c * F l
    cases l <;> cases h : g.c <;>
      simp [f_form,add_mul,mul_add,single_slide,signAt,h,Coset.signX,Coset.signY,
        add_comm,add_left_comm,add_assoc]

theorem shift_add (a : Axis) (n m : ℤ) : shift a n * shift a m = shift a (n+m) := by
  cases a <;> simp [shift,tr,single_mul_single,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
    ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ]

theorem shift_zero (a : Axis) : shift a 0 = 1 := by cases a <;> rfl

theorem shift_factor (l : Letter) : shift l.axis l.degree * F l =
    1 + shifts l.axis (if l = .A' then [1,2,3,4] else [1,2]) := by
  cases l <;> simp [f_form,Letter.axis,Letter.degree,mul_add,shift_add,shifts,shift_zero,
    List.map]

def multiples (d : IntegralGroupRing) : AddSubgroup IntegralGroupRing where
  carrier := {v | ∃ t, v = d*t}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by rintro a b ⟨p,rfl⟩ ⟨q,rfl⟩; exact ⟨p+q,(mul_add ..).symm⟩
  neg_mem' := by rintro a ⟨p,rfl⟩; exact ⟨-p,(mul_neg ..).symm⟩

def preserves (a : Axis) : Subring IntegralGroupRing where
  carrier := {d | ∀ j r, slice a j (d*r) = d*slice a j r}
  one_mem' := by simp
  zero_mem' := by intro j r; ext g; simp [slice_apply]
  add_mem' := by rintro d e hd he j r; rw [add_mul,slice_add,hd,he,add_mul]
  mul_mem' := by rintro d e hd he j r; rw [mul_assoc,hd,he,mul_assoc]
  neg_mem' := by
    rintro d hd j r
    have negS (z : IntegralGroupRing) : slice a j (-z) = -slice a j z := by
      ext g
      simp only [slice_apply]
      split <;> simp_all [slice_apply]
    rw [neg_mul,negS,hd,neg_mul]

theorem shift_preserves {a b : Axis} (h : a ≠ b) (n : ℤ) : shift a n ∈ preserves b := by
  intro j r
  simpa [h] using slice_shift a b n j r

theorem factor_preserves (l : Letter) : F l ∈ preserves (other l.axis) := by
  have h : l.axis ≠ other l.axis := by cases l <;> decide
  have hh := shift_preserves h
  cases l <;> simp only [f_form, Letter.axis, other] at hh ⊢ <;>
    repeat' first | apply Subring.add_mem | apply hh

theorem cancel_factor (l : Letter) (d : IntegralGroupRing) (hd : d ∈ preserves l.axis)
    (cd : ∀ a, Commute d a) (r : IntegralGroupRing) (h : F l * r ∈ multiples d) :
    r ∈ multiples d := by
  let H := multiples d
  have shiftH (n : ℤ) (v : IntegralGroupRing) (hv : v∈H) : shift l.axis n*v∈H := by
    rcases hv with ⟨t,rfl⟩
    exact ⟨shift l.axis n*t,(cd _).symm.left_comm _⟩
  apply recurrence l.axis H (fun j _ ⟨t,ht⟩ => ⟨slice l.axis j t,ht ▸ hd j t⟩) shiftH
    (if l=.A' then [1,2,3,4] else [1,2]) (by cases l <;> simp) r
  rw [← shift_factor,mul_assoc]
  exact shiftH _ _ h

theorem regularF (l : Letter) (r : IntegralGroupRing) (h : F l * r = 0) : r = 0 := by
  have hh := cancel_factor l 0 (Subring.zero_mem _) (fun _ => Commute.zero_left _) r
    (show F l * r ∈ multiples 0 from ⟨0,by simpa using h⟩)
  obtain ⟨t,ht⟩ := hh
  simpa using ht

end
end Promislow
