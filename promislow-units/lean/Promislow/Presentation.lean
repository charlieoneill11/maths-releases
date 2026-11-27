import Promislow.Group
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

namespace Promislow.Presentation
noncomputable section

def relA {G : Type*} [Group G] (a b : G) := a⁻¹*b^2*a*b^2
def relB {G : Type*} [Group G] (a b : G) := b⁻¹*a^2*b*a^2

private abbrev A₀ := FreeGroup.of false
private abbrev B₀ := FreeGroup.of true
def rels : Set (FreeGroup Bool) := {relA A₀ B₀, relB A₀ B₀}
abbrev P := PresentedGroup rels
abbrev a : P := PresentedGroup.of false
abbrev b : P := PresentedGroup.of true
private theorem rel1 : relA a b=1 := by
  have h := PresentedGroup.one_of_mem (rels := rels) (x := relA A₀ B₀) (by simp [rels])
  simpa [relA,PresentedGroup.of] using h
private theorem rel2 : relB a b=1 := by
  have h := PresentedGroup.one_of_mem (rels := rels) (x := relB A₀ B₀) (by simp [rels])
  simpa [relB,PresentedGroup.of] using h

def generators : Bool → ElemP
  | false => ElemP.genA | true => ElemP.genB

def coordinates : P →* ElemP :=
  PresentedGroup.toGroup (f := generators) (by
    intro r hr
    rcases hr with h|h
    · subst r; simp [relA]; decide
    · change r=relB A₀ B₀ at h
      subst r; simp [relB]; decide)

@[simp] theorem coordinates_gen (j : Bool) : coordinates (PresentedGroup.of j) = generators j :=
  PresentedGroup.toGroup.of _

private abbrev x := a^2
private abbrev y := b^2
private abbrev z := (a*b)^2

/-- Normalize the freely reduced products in the relator certificates below. -/
local macro "reduce_word" : tactic =>
  `(tactic| simp only [x,y,z,relA,relB,pow_two,mul_inv_rev,inv_inv,mul_assoc,
        mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one,one_mul])

private theorem xy : Commute x y := by
  apply eq_of_mul_inv_eq_one
  calc
    (x*y)*(y*x)⁻¹ = ((a*b⁻¹*b⁻¹*a)*(relA a b)*(a*b⁻¹*b⁻¹*a)⁻¹) * ((a)*(relA a b)⁻¹*(a)⁻¹) := by
      reduce_word
    _ = 1 := by simp only [rel1]; group

private theorem xz : Commute x z := by
  apply eq_of_mul_inv_eq_one
  calc
    (x*z)*(z*x)⁻¹ = ((a*b)*(relB a b)*(a*b)⁻¹) * ((a*b*a⁻¹*b)*(relB a b)⁻¹*(a*b*a⁻¹*b)⁻¹) := by
      reduce_word
    _ = 1 := by simp only [rel2]; group

private theorem yz : Commute y z := by
  apply eq_of_mul_inv_eq_one
  calc
    (y*z)*(z*y)⁻¹ = ((a)*(relA a b)*(a)⁻¹) * ((a*b⁻¹*a)*(relA a b)⁻¹*(a*b⁻¹*a)⁻¹) := by
      reduce_word
    _ = 1 := by simp only [rel1]; group

private theorem ba : b*a=x⁻¹*y*z⁻¹*(a*b) := by
  apply eq_of_mul_inv_eq_one
  calc
    (b*a)*(x⁻¹*y*z⁻¹*(a*b))⁻¹ = ((b*a*a)*(relB a b)*(b*a*a)⁻¹) := by
      reduce_word
    _ = 1 := by simp only [rel2]; group

private theorem aba : a*b*a=y⁻¹*z*b := by
  apply eq_of_mul_inv_eq_one
  calc
    (a*b*a)*(y⁻¹*z*b)⁻¹ = ((a*b*a*b⁻¹*b⁻¹*a⁻¹*b⁻¹)*(relA a b)*(a*b*a*b⁻¹*b⁻¹*a⁻¹*b⁻¹)⁻¹) * ((a*b*a)*(relA a b)⁻¹*(a*b*a)⁻¹) := by
      reduce_word
    _ = 1 := by simp only [rel1]; group

private theorem abb : a*b*b=y⁻¹*a := by
  apply eq_of_mul_inv_eq_one
  calc
    (a*b*b)*(y⁻¹*a)⁻¹ = ((a*b*b)*(relA a b)*(a*b*b)⁻¹) := by
      reduce_word
    _ = 1 := by simp only [rel1]; group

private def T (i j k : ℤ) : P := x^i*y^j*z^k

private theorem T_add (i j k d e f : ℤ) : T (i+d) (j+e) (k+f)=T i j k * T d e f := by
  simp only [T,zpow_add,mul_assoc]
  rw [(yz.zpow_zpow e k).left_comm,(xy.zpow_zpow d j).left_comm,(xz.zpow_zpow d k).left_comm]

private def repr : Coset → P
  | .e => 1 | .a => a | .b => b | .ab => a*b

def evaluate (g : ElemP) : P := T g.ix g.iy g.iz * repr g.c

private def base (c : Coset) : ElemP := ⟨0,0,0,c⟩

private theorem collect (c : Coset) (j : Bool) :
    evaluate (base c * generators j) = repr c * PresentedGroup.of j := by
  cases c <;> cases j <;>
    change T _ _ _ * _ = _ <;>
    first
    | exact (by simpa [T] using ba.symm)
    | exact (by simpa [T] using aba.symm)
    | exact (by simpa [T] using abb.symm)
    | simp [T,repr,generators,base,ElemP.genA,ElemP.genB,
        show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
        ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ,x,y,pow_two,
        a,b]

private theorem right_generator (g : ElemP) (j : Bool) :
    evaluate (g*generators j) = evaluate g * PresentedGroup.of j := by
  let t := base g.c * generators j
  have shift : g*generators j = ⟨g.ix+t.ix,g.iy+t.iy,g.iz+t.iz,t.c⟩ := by
    obtain ⟨i,k,l,c⟩ := g
    cases c <;> cases j <;>
      simp [t,base,generators,ElemP.genA,ElemP.genB,
        show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
        ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ]
  rw [shift]
  change T (g.ix+t.ix) (g.iy+t.iy) (g.iz+t.iz)*repr t.c=_
  rw [T_add,mul_assoc]
  change T g.ix g.iy g.iz * evaluate (base g.c*generators j) = _
  rw [collect,← mul_assoc]; rfl

private def good : Subgroup P where
  carrier := {h | ∀ g : ElemP, evaluate (g*coordinates h)=evaluate g * h}
  one_mem' := by intro g; simp
  mul_mem' := by
    intro u v hu hv g
    change ∀ g, _ at hu hv
    rw [map_mul,← mul_assoc,hv,hu,mul_assoc]
  inv_mem' := by
    intro u hu g
    change ∀ g, _ at hu
    apply mul_right_cancel (b := u)
    rw [← hu, map_inv]; simp [mul_assoc]

theorem evaluate_coordinates (h : P) : evaluate (coordinates h) = h := by
  have hg := PresentedGroup.generated_by rels good (fun j => by
    intro g; rw [coordinates_gen]; exact right_generator g j) h
  change ∀ g, evaluate (g*coordinates h)=evaluate g*h at hg
  have h1 : evaluate 1=1 := by change T 0 0 0*1=1; simp [T]
  simpa only [one_mul,h1] using hg 1

private theorem power_translation (i j k n : ℤ) :
    (⟨i,j,k,.e⟩ : ElemP)^n = ⟨n*i,n*j,n*k,.e⟩ := by
  cases n with
  | ofNat m => rw [show (Int.ofNat m)=(m:ℤ) from rfl,zpow_natCast,pow_eq,ElemP.pow_of_e]
  | negSucc m =>
    rw [zpow_negSucc,pow_eq,ElemP.pow_of_e]
    change ElemP.inv _=_
    simp [ElemP.inv,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ,Int.negSucc_eq]
    ring_nf
    simp

theorem coordinates_evaluate (g : ElemP) : coordinates (evaluate g)=g := by
  have hx : coordinates x=ElemP.genX := by rw [map_pow]; rfl
  have hy : coordinates y=ElemP.genY := by rw [map_pow]; rfl
  have hz : coordinates z=ElemP.genZ := by rw [map_pow,map_mul]; rfl
  have hr (c : Coset) : coordinates (repr c)=base c := by
    cases c <;> simp [repr,base,a,b,coordinates_gen,generators,map_mul] <;> rfl
  obtain ⟨i,j,k,c⟩ := g
  change coordinates (T i j k * repr c) = _
  rw [map_mul,hr]
  simp only [T,map_mul,map_zpow,hx,hy,hz,ElemP.genX,ElemP.genY,ElemP.genZ,power_translation]
  cases c <;> simp [base,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
    ElemP.mul,Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ]

/-- Gardam's two-relator presentation has exactly the triples and four cosets of the model. -/
def equiv : P ≃* ElemP where
  toFun := coordinates
  invFun := evaluate
  left_inv := evaluate_coordinates
  right_inv := coordinates_evaluate
  map_mul' := coordinates.map_mul

end
end Promislow.Presentation
