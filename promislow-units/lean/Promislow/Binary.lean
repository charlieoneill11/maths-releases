import Promislow.Sign
import Mathlib.Tactic.Ring

namespace Promislow.Binary
open MonoidAlgebra
abbrev K := ZMod 2
abbrev R₂ := MonoidAlgebra K ElemP
abbrev Site := Coset × ZMod 7
abbrev Row := Site → K

/-- Right action on the four cosets with translation exponents read modulo seven. -/
def grade (g : ElemP) : ZMod 7 := (g.ix+2*g.iy+3*g.iz : ℤ)
def act (s : Site) (g : ElemP) : Site :=
  let t := Image.rep s.1*g
  (t.c,s.2+grade t)

private theorem splitGrade (p h : ElemP) :
    (p*h).c=(Image.rep p.c*h).c ∧ grade (p*h)=grade p+grade (Image.rep p.c*h) := by
  obtain ⟨x,y,z,c⟩ := p
  obtain ⟨i,j,k,s⟩ := h
  cases c <;> cases s <;>
    simp [grade,Image.rep,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
      ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ] <;> ring

theorem act_mul (s : Site) (g h : ElemP) : act s (g*h)=act (act s g) h := by
  obtain ⟨c,k⟩ := s
  obtain ⟨hc,hk⟩ := splitGrade (Image.rep c*g) h
  simp only [act,← mul_assoc,hc,hk,add_assoc]

theorem act_one (s : Site) : act s 1=s := by
  obtain ⟨c,k⟩ := s
  simp [act,Image.rep,grade]

noncomputable def readRow (f : Row) (s : Site) : R₂ →+ K :=
  Finsupp.liftAddHom fun g => AddMonoidHom.mulRight (f (act s g⁻¹))
noncomputable def push (p : R₂) (f : Row) (s : Site) := readRow f s p

@[simp] private theorem push_zero (f : Row) (s : Site) : push 0 f s=0 := (readRow f s).map_zero
@[simp] private theorem push_add (p q : R₂) (f : Row) (s : Site) :
    push (p+q) f s=push p f s+push q f s := (readRow f s).map_add p q
@[simp] private theorem push_single (g : ElemP) (a : K) (f : Row) (s : Site) :
    push (single g a) f s=a*f (act s g⁻¹) := by
  exact Finsupp.liftAddHom_apply_single _ _ _
@[simp] private theorem push_one (f : Row) (s : Site) : push 1 f s=f s := by
  change push (single 1 1) f s=_
  rw [push_single,inv_one,act_one,one_mul]

private theorem push_mul (p q : R₂) (f : Row) (s : Site) : push (p*q) f s=push q (push p f) s := by
  induction q using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => simp [mul_add,hu,hv]
  | single h d =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u v hu hv => simp_all [add_mul,mul_add]
    | single g c => simp [single_mul_single,act_mul,mul_comm,mul_assoc]

def advance (p : Sparse.Poly) (f : Row) (s : Site) : K :=
  p.foldr (fun (g,c) r => (c:K)*f (act s g⁻¹)+r) 0

private theorem advance_ok (p : Sparse.Poly) (f : Row) (s : Site) :
    advance p f s=push (modTwo (Sparse.val p)) f s := by
  induction p with
  | nil => simp [advance,Sparse.val]
  | cons t q ih =>
    obtain ⟨g,c⟩ := t
    change (c:K)*f (act s g⁻¹)+advance q f s=_
    simp only [Sparse.val,map_add,push_add,ih]
    simp only [modTwo,mapRangeRingHom_single,push_single,Int.coe_castRingHom]

abbrev Block := Image.Four (Vector K 7)
def pack (f : Row) : Block := Image.four fun c => Vector.ofFn (fun k : Fin 7 => f (c,k))
def unpack (b : Block) (s : Site) : K := (b.get s.1).get s.2
theorem unpack_pack (f : Row) : unpack (pack f)=f := by
  funext s; obtain ⟨c,k⟩ := s; cases c <;> simp [unpack,pack,Image.four,Image.Four.get,Vector.get]

def run (b : Block) : List Sparse.Poly → Block
  | [] => b
  | p::ps => run (pack (advance p (unpack b))) ps

theorem run_ok (ps : List Sparse.Poly) (b : Block) :
    unpack (run b ps) = push (modTwo ((ps.map Sparse.val).prod)) (unpack b) := by
  induction ps generalizing b with
  | nil => funext s; simp [run]
  | cons p ps ih =>
    rw [run,ih,unpack_pack]
    have val : advance p (unpack b)=push (modTwo (Sparse.val p)) (unpack b) :=
      funext (advance_ok p (unpack b))
    funext s
    rw [val,List.map_cons,List.prod_cons,map_mul,push_mul]

def seed : Block := pack (fun s => if s=(.e,0) then 1 else 0)
def nums := whole.map fun (l,r) => Sparse.num l r
def dens := whole.map fun (l,_) => Sparse.pow (Sparse.factor l) 4

theorem nums_ok : (nums.map Sparse.val).prod = wordN whole := by
  simp [nums,wordN,N,List.map_map,Function.comp_def]
theorem dens_ok : (dens.map Sparse.val).prod = wordD whole := by
  simp [dens,wordD,F,List.map_map,Function.comp_def,Sparse.val_pow]

private theorem denominator_row : run seed dens=seed := by native_decide

private theorem numerator_sites :
    let r := unpack (run seed nums)
    r (.e,0)=1 ∧ r (.a,0)=1 := by native_decide

/-- The image of the cleared numerator occupies two sites. Each group element
acts on the 28 sites by a permutation, and the denominator fixes the seed row. -/
theorem not_basis (u : IntegralGroupRing) (eqn : wordD whole*u=wordN whole) (g : ElemP) :
    modTwo u ≠ single g 1 := by
  intro h
  have dn := run_ok dens seed
  rw [dens_ok,denominator_row] at dn
  have nu := run_ok nums seed
  rw [nums_ok,← eqn,map_mul,h] at nu
  have coeff (s : Site) : unpack (run seed nums) s=unpack seed (act s g⁻¹) := by
    simpa only [push_mul,← dn,push_single,one_mul] using congrFun nu s
  have pre (s : Site) (nonzero : unpack (run seed nums) s=1) : act s g⁻¹=(.e,0) := by
    by_contra ne
    rw [coeff,seed,unpack_pack,if_neg ne] at nonzero
    exact zero_ne_one nonzero
  have eq := (pre _ numerator_sites.1).trans (pre _ numerator_sites.2).symm
  have eq' := congrArg (fun s => act s g) eq
  simp only [← act_mul,inv_mul_cancel,act_one] at eq'
  exact (by decide : ((Coset.e,0) : Site) ≠ (.a,0)) eq'

end Promislow.Binary
