import Promislow.Word
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

namespace Promislow.Image
open Promislow MonoidAlgebra
abbrev k := ZMod 17

instance : Fintype Coset where
  elems := {.e,.a,.b,.ab}
  complete := by intro i; cases i <;> decide

abbrev Mat := Matrix Coset Coset k

def rep (i : Coset) : ElemP := ⟨0,0,0,i⟩

def ux : kˣ := ⟨2,9,by decide,by decide⟩
def uy : kˣ := ⟨3,6,by decide,by decide⟩
def uz : kˣ := ⟨5,7,by decide,by decide⟩

def weight (g : ElemP) : k := ↑(ux^g.ix * uy^g.iy * uz^g.iz)

def M (g : ElemP) : Mat := fun i j =>
  let t := rep i*g
  if t.c=j then weight t else 0

private theorem block (p h : ElemP) :
    (p*h).c = (rep p.c*h).c ∧ weight (p*h) = weight p * weight (rep p.c*h) := by
  obtain ⟨x,y,z,c⟩ := p
  obtain ⟨i,j,k,s⟩ := h
  have shiftCoord (c s : Coset) (x y z i j k : ℤ) :
      let t := rep c * (⟨i,j,k,s⟩:ElemP)
      (⟨x,y,z,c⟩:ElemP)*⟨i,j,k,s⟩ = ⟨x+t.ix,y+t.iy,z+t.iz,t.c⟩ := by
    cases c <;> cases s <;> simp [rep,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
      ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ] <;> omega
  rw [shiftCoord]
  constructor
  · rfl
  · simp [weight,zpow_add,rep,mul_left_comm,mul_assoc]

def matrixHom : ElemP →* Mat where
  toFun := M
  map_one' := by
    ext i j
    cases i <;> cases j <;> decide
  map_mul' g h := by
    ext i j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (rep i*g).c]
    · obtain ⟨e,w⟩ := block (rep i*g) h
      simp only [M,← mul_assoc,e,w]
      split <;> simp_all
    · intro c _ hne
      change (if (rep i*g).c=c then _ else 0) * _ = _
      rw [if_neg (Ne.symm hne),zero_mul]
    · simp

noncomputable def ρ : IntegralGroupRing →+* Mat :=
  liftNCRingHom (Int.castRingHom Mat) matrixHom (fun i g => Int.cast_commute i (matrixHom g))

theorem rho_single (g : ElemP) (i : ℤ) : ρ (single g i) = (i:Mat)*M g := by
  simp [ρ, matrixHom]

def table : Sparse.Poly → Mat
  | [] => 0
  | (g,c)::xs => (c:Mat)*M g + table xs

theorem table_ok (p : Sparse.Poly) : ρ (Sparse.val p) = table p := by
  induction p with
  | nil => simp [Sparse.val,table]
  | cons t xs ih => rcases t with ⟨g,c⟩; simp [Sparse.val,table,rho_single,ih]

def numerator (w : Word) : Mat :=
  (w.map fun (l,r) => table (Sparse.num l r)).prod
def denominator (w : Word) : Mat :=
  (w.map fun (l,_) => (table (Sparse.factor l))^4).prod

theorem evalN (w : Word) : ρ (wordN w) = numerator w := by
  induction w with
  | nil => simp [wordN,numerator]
  | cons t xs ih =>
    rcases t with ⟨l,r⟩
    change ρ (N l r * wordN xs) = _ * numerator xs
    rw [map_mul,ih,N,table_ok]

theorem evalD (w : Word) : ρ (wordD w) = denominator w := by
  induction w with
  | nil => simp [wordD,denominator]
  | cons t xs ih =>
    rcases t with ⟨l,r⟩
    change ρ (F l^4 * wordD xs) = _ * denominator xs
    rw [map_mul,map_pow,ih,F,table_ok]

/-- Strict data keep long matrix products linear in the word length. -/
structure Four (α : Type) where
  e : α
  a : α
  b : α
  ab : α
  deriving DecidableEq

def Four.get {α} (v : Four α) : Coset → α
  | .e => v.e | .a => v.a | .b => v.b | .ab => v.ab
def four {α} (v : Coset → α) : Four α := ⟨v .e,v .a,v .b,v .ab⟩

abbrev Block := Four (Four k)
def unpack (b : Block) : Mat := fun i j => (b.get i).get j
def blockOf (m : Mat) : Block := four fun i => four (m i)
theorem unpack_blockOf (m : Mat) : unpack (blockOf m)=m := by
  funext i j; cases i <;> cases j <;> rfl

def product : List Block → Block
  | [] => blockOf 1
  | b::bs => blockOf (unpack b * unpack (product bs))

theorem product_eq (ms : List Block) : unpack (product ms) = (ms.map unpack).prod := by
  induction ms with
  | nil => exact unpack_blockOf _
  | cons m ms ih => simp [product,unpack_blockOf,ih]

def rowEntry (p : Sparse.Poly) (i j : Coset) : k :=
  p.foldr (fun (g,c) r => (c:k)*M g i j+r) 0

theorem rowEntry_ok (p : Sparse.Poly) (i j : Coset) : rowEntry p i j=table p i j := by
  induction p with
  | nil => rfl
  | cons t xs ih =>
    rcases t with ⟨g,c⟩
    change (c:k)*M g i j+rowEntry xs i j=((c:Mat)*M g+table xs) i j
    rw [ih]
    simp [← Matrix.diagonal_intCast, Matrix.diagonal_mul]

theorem rows_ok (p : Sparse.Poly) : rowEntry p = table p := by
  funext i j
  exact rowEntry_ok p i j

def cachedLetter (l : Letter) (r : Bool) : Block := blockOf (rowEntry (Sparse.num l r))

def cachedDivisor (l : Letter) : Block :=
  let mat := blockOf (rowEntry (Sparse.factor l))
  let sq := blockOf (unpack mat * unpack mat)
  blockOf (unpack sq * unpack sq)

theorem cachedN (w : Word) :
    numerator w = unpack (product (w.map fun (l,r) => cachedLetter l r)) := by
  rw [product_eq]
  simp [numerator,List.map_map,Function.comp_def,cachedLetter,unpack_blockOf,rows_ok]

theorem cachedD (w : Word) :
    denominator w = unpack (product (w.map fun (l,_) => cachedDivisor l)) := by
  rw [product_eq]
  simp [denominator,List.map_map,Function.comp_def,cachedDivisor,unpack_blockOf,rows_ok,
    pow_succ,mul_assoc]

def pack {α} (e a b ab : α) : Coset → α := (Four.mk e a b ab).get

def Umat : Mat := pack (pack 11 16 1 12) (pack 4 8 8 13) (pack 5 15 8 11) (pack 10 3 12 11)
def Vmat : Mat := pack (pack 8 1 16 5) (pack 13 11 9 4) (pack 12 2 11 6) (pack 7 14 5 8)

private theorem unpack_eq {b : Block} {m : Mat} (h : b=blockOf m) : unpack b=m := by
  rw [h,unpack_blockOf]

theorem full_num_image : numerator whole = Umat :=
  (cachedN whole).trans (unpack_eq (by native_decide))

theorem num_image : numerator whole .e .e = 11 ∧ numerator whole .e .a = 16 := by
  rw [full_num_image]; decide

theorem den_image : denominator whole = 1 := by
  exact (cachedD whole).trans (unpack_eq (by native_decide))

theorem not_signed (u : IntegralGroupRing) (hu : wordD whole * u = wordN whole) (g : ElemP) :
    u ≠ single g 1 ∧ u ≠ -single g 1 := by
  have img := congrArg ρ hu
  rw [map_mul,evalD,evalN,den_image,one_mul] at img
  have off (i : Coset) (h : g.c ≠ i) : M g .e i=0 := by
    change (if ((1:ElemP)*g).c=i then _ else _) = 0
    simp [h]
  have witness : ∃ i, g.c ≠ i ∧ numerator whole .e i ≠ 0 := by
    by_cases hg : g.c=.e
    · exact ⟨.a,by simp [hg],by rw [num_image.2];decide⟩
    · exact ⟨.e,hg,by rw [num_image.1];decide⟩
  obtain ⟨i,hi,hn⟩ := witness
  constructor
  · intro e
    rw [e,rho_single,Int.cast_one,one_mul] at img
    exact hn (img ▸ off i hi)
  · intro e
    rw [e,map_neg,rho_single,Int.cast_one,one_mul] at img
    apply hn
    rw [← img]
    change -(M g .e i)=0
    simp [off i hi]

end Promislow.Image
