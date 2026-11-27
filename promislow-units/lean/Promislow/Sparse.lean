import Promislow.Group

namespace Promislow.Sparse

abbrev Term := ElemP × ℤ
abbrev Poly := List Term

noncomputable def val : Poly → IntegralGroupRing
  | [] => 0
  | (g,c)::xs => MonoidAlgebra.single g c + val xs

def before (g h : ElemP) : Bool :=
  if g.c.toNat != h.c.toNat then g.c.toNat < h.c.toNat
  else if g.ix != h.ix then g.ix < h.ix
  else if g.iy != h.iy then g.iy < h.iy
  else g.iz < h.iz

def insert (g : ElemP) (c : ℤ) : Poly → Poly
  | [] => if c = 0 then [] else [(g,c)]
  | (h,d)::t =>
    if g = h then if c+d = 0 then t else (g,c+d)::t
    else if before g h then
      if c = 0 then (h,d)::t else (g,c)::(h,d)::t
    else (h,d)::insert g c t

theorem val_insert (g : ElemP) (c : ℤ) (p : Poly) :
    val (insert g c p) = MonoidAlgebra.single g c + val p := by
  induction p with
  | nil => by_cases h : c = 0 <;> simp [insert,h,val]
  | cons a t ih =>
    obtain ⟨h,d⟩ := a
    by_cases eq : g = h
    · subst h
      by_cases z : c+d=0
      · simp [insert, val, ← add_assoc, ← MonoidAlgebra.single_add, z]
      · simp [insert,z,val,← add_assoc,← MonoidAlgebra.single_add]
    · simp only [insert, if_neg eq]
      split
      · by_cases z : c=0 <;> simp [z,val]
      · simp [val,ih,add_left_comm]

def add (x y : Poly) : Poly := x.foldr (fun t r => insert t.1 t.2 r) y

theorem val_add (x y : Poly) : val (add x y) = val x + val y := by
  induction x with
  | nil => simp [add,val]
  | cons t xs ih =>
    rcases t with ⟨g,c⟩
    change val (insert g c (add xs y)) = _
    rw [val_insert,ih]; simp [val,add_assoc]

def mulTerm (g : ElemP) (c : ℤ) (p : Poly) : Poly :=
  p.foldr (fun t r => insert (g*t.1) (c*t.2) r) []

theorem val_mulTerm (g : ElemP) (c : ℤ) (p : Poly) :
    val (mulTerm g c p) = MonoidAlgebra.single g c * val p := by
  induction p with
  | nil => simp [mulTerm,val]
  | cons t xs ih =>
    obtain ⟨h,d⟩ := t
    change val (insert (g*h) (c*d) (mulTerm g c xs)) = _
    rw [val_insert,ih]; simp [val,mul_add,MonoidAlgebra.single_mul_single]

def mul (p q : Poly) : Poly :=
  p.foldr (fun t r => add (mulTerm t.1 t.2 q) r) []

theorem val_mul (x y : Poly) : val (mul x y) = val x * val y := by
  induction x with
  | nil => simp [mul,val]
  | cons t xs ih =>
    obtain ⟨g,c⟩ := t
    change val (add (mulTerm g c y) (mul xs y)) = _
    rw [val_add,val_mulTerm,ih]; simp [val,add_mul]

def atom (g : ElemP) (c : ℤ := 1) : Poly := [(g,c)]

theorem val_atom (g : ElemP) (c : ℤ) : val (atom g c) = MonoidAlgebra.single g c := by
  simp [atom,val]

def one : Poly := atom 1
theorem val_one : val one = 1 := by rw [one,val_atom]; rfl

def pow (p : Poly) : ℕ → Poly
  | 0 => one
  | n+1 => mul (pow p n) p

theorem val_pow (p : Poly) (n : ℕ) : val (pow p n) = val p ^ n := by
  induction n with
  | zero => simp [pow,val_one]
  | succ n ih => simp [pow,val_mul,ih,pow_succ]

end Promislow.Sparse
