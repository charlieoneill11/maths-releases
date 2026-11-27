import Promislow.Image
import Promislow.Recorded
import Promislow.Integrality
import Mathlib.Algebra.MonoidAlgebra.MapDomain

namespace Promislow
noncomputable section
open MonoidAlgebra

def signedGroup : ElemP →* IntegralGroupRing where
  toFun g := single g g.c.signY
  map_one' := rfl
  map_mul' g h := by
    rw [single_mul_single]
    congr 1
    exact Coset.signY_mul g.c h.c

def twist : IntegralGroupRing →+* IntegralGroupRing :=
  liftNCRingHom (Int.castRingHom _) signedGroup (fun i _ => Int.cast_commute i _)

theorem twist_single (g : ElemP) (c : ℤ) : twist (single g c)=single g (c*g.c.signY) := by
  simp [twist,signedGroup,MonoidAlgebra.intCast_def,single_mul_single]

def modTwo : IntegralGroupRing →+* MonoidAlgebra (ZMod 2) ElemP :=
  mapRangeRingHom ElemP (Int.castRingHom (ZMod 2))

theorem modTwo_twist (x : IntegralGroupRing) : modTwo (twist x)=modTwo x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb]
  | single g c =>
    simp only [twist_single,modTwo,mapRangeRingHom_single,map_mul]
    have h : (Int.castRingHom (ZMod 2)) g.c.signY = 1 := by cases g.c <;> decide
    rw [h,mul_one]

namespace Image

def J : Mat := Matrix.diagonal fun (c : Coset) => (c.signY:k)

theorem twist_image (r : IntegralGroupRing) : ρ (twist r)=J*ρ r*J := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,mul_add,add_mul]
  | single g c =>
    rw [twist_single,rho_single,rho_single]
    ext i j
    simp only [J,← Matrix.diagonal_intCast,Matrix.mul_diagonal,Matrix.diagonal_mul,Int.cast_mul]
    rcases g with ⟨x,y,z,t⟩
    cases i <;> cases j <;> cases t <;>
      simp [M,rep,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,ElemP.mul,
        Coset.mulCocycle,Coset.signY]

theorem eval_sign_witness {u v : IntegralGroupRing} (hu : ρ u = Umat) (huv : u*v=1) :
    ρ (u*twist v) = Umat*J*Vmat*J := by
  have vu : Vmat*Umat=1 := by
    apply unpack_eq' ; native_decide
  have hv : ρ v = Vmat := by
    have eqn := congrArg ρ huv
    rw [map_mul,hu,map_one] at eqn
    calc
      _ = (Vmat*Umat)*ρ v := by rw [vu,one_mul]
      _ = _ := by rw [mul_assoc,eqn,mul_one]
  rw [map_mul,hu,twist_image,hv]
  simp [mul_assoc]
where
  unpack_eq' {a b : Mat} (h : blockOf a=blockOf b) : a=b := by
    simpa only [unpack_blockOf] using congrArg unpack h

theorem sign_not_signed {w : IntegralGroupRing} (hw : ρ w=Umat*J*Vmat*J) (g : ElemP) :
    w ≠ single g 1 ∧ w ≠ -single g 1 := by
  have off (i : Coset) (h : g.c ≠ i) : M g .e i=0 := by
    change (if ((1:ElemP)*g).c=i then _ else _) = 0
    simp [h]
  have sample : (Umat*J*Vmat*J) .e .e = 12 ∧ (Umat*J*Vmat*J) .e .a = 8 := by native_decide
  have witness : ∃ i, g.c ≠ i ∧ (Umat*J*Vmat*J) .e i ≠ 0 := by
    by_cases h : g.c=.e
    · exact ⟨.a,by simp [h],by rw [sample.2];decide⟩
    · exact ⟨.e,h,by rw [sample.1];decide⟩
  obtain ⟨i,hi,hn⟩ := witness
  constructor
  · intro e; rw [e,rho_single,Int.cast_one,one_mul] at hw; exact hn (hw ▸ off i hi)
  · intro e; rw [e,map_neg,rho_single,Int.cast_one,one_mul] at hw
    apply hn; rw [← hw]; change -(M g .e i)=0; simp [off i hi]

end Image
end
end Promislow
