import Promislow.Contact
import Promislow.Units
import Promislow.Midpoint

namespace Promislow
noncomputable section
open Sparse
namespace Ambient
variable {S : Type*} [Ring S] (E : Ambient S)

def p (l : Letter) (r : Bool) : S := E.ι (val (scalarPart l r))*↑(E.den l)⁻¹

theorem split_local {l f : Letter} (h : l.axis ≠ f.axis) (r : Bool) :
    ∃ q ∈ E.localOrder f, ∃ t ∈ E.localOrder f,
      ((signed (E.L l) r : Sˣ):S) = E.p l r + E.f f^5*q ∧
      E.p l r = 1 + E.f f*t := by
  have hl : l≠f := fun e => h (congrArg Letter.axis e)
  let di : S := ↑(E.den l)⁻¹
  have hdi : di∈E.localOrder f := E.denInv_local hl
  obtain ⟨a,b⟩ := transverse l f r h
  refine ⟨E.ι (val (screwQuot l f r))*di,(E.localOrder f).mul_mem (E.base_local _ _) hdi,
    E.ι (val (scalarQuot l f r))*di,(E.localOrder f).mul_mem (E.base_local _ _) hdi,?_,?_⟩
  · rw [E.letter_value,a,map_add,map_mul,map_pow,add_mul,mul_assoc]
    rfl
  · unfold p
    rw [b,map_add,map_pow,map_mul,add_mul,mul_assoc]
    change E.f l^4*↑(E.den l)⁻¹ + _ = _
    rw [← E.den_coe, Units.mul_inv]
    rfl

theorem p_commutes {l v : Letter} (h : l.axis ≠ v.axis) (r : Bool) :
    Commute (E.p l r) (E.C v:S) ∧ Commute (E.p l r) (E.K v:S) ∧
    Commute (E.p l r) (E.L v:S) := by
  obtain ⟨a,b,c⟩ := transverse_commutes l v r h
  refine ⟨(a.map E.ι).mul_left ((E.den_c l _).units_inv_left),
    (b.map E.ι).mul_left ((E.den_c l _).units_inv_left),?_⟩
  change Commute (E.p l r) ((signed (E.L v) false:Sˣ):S)
  rw [E.letter_value]
  exact ((c.map E.ι).mul_left ((E.den_c l _).units_inv_left)).mul_right
    ((E.den_c v _).units_inv_left.symm)

theorem halves_near {l f : Letter} (h : l.axis ≠ f.axis) (r : Bool) :
    Near (E.localOrder f) (E.f f) 1 (conjugate (E.C f)⁻¹ (signed (E.L l) r):S) ∧
    Near (E.localOrder f) (E.f f) 1 (conjugate (E.K f) (signed (E.L l) r):S) := by
  obtain ⟨q,hq,t,ht,e,pq⟩ := E.split_local h r
  obtain ⟨hc,hk,hci,hki⟩ := E.half_local f
  obtain ⟨cp,kp,_⟩ := E.p_commutes h r
  constructor
  · simpa only [conjugate,Units.val_mul,inv_inv] using
      (half_conjugates (E.central f) hc hci cp e pq hq ht).2
  · exact (half_conjugates (E.central f) hk hki kp e pq hq ht).1

theorem halfUnits_near {l f : Letter} (h : l.axis ≠ f.axis) :
    NearUnit (E.localOrder f) (E.f f) 1 (conjugate (E.C f)⁻¹ (E.L l)) ∧
    NearUnit (E.localOrder f) (E.f f) 1 (conjugate (E.K f) (E.L l)) := by
  have a := E.halves_near h false
  have b := E.halves_near h true
  simp only [signed, Bool.false_eq_true, if_false,if_true] at a b
  exact ⟨⟨a.1,by rw [conjugate_inv]; exact b.1⟩,⟨a.2,by rw [conjugate_inv]; exact b.2⟩⟩

def W (l : Letter) : Sˣ := commWord (E.L l) (E.L .B)

private theorem denComm (l : Letter) (x : Sˣ) : Commute (E.den l) x :=
  Units.ext ((E.den_c l (x:S)).eq)

private theorem cancel_conjugate (f : Letter) (b : Sˣ) :
    conjugate (E.C f)⁻¹ (commWord (E.L f) b) =
    conjugate (E.K f) b * (conjugate (E.C f)⁻¹ b)⁻¹ := by
  have c := (E.denComm f b).inv_left
  simp [L,conjugate,commWord,mul_assoc,c.left_comm]

theorem localW (l : Letter) (hl : l≠.B) (f : Letter) :
    NearUnit (E.localOrder f) (E.f f) 1 (conjugate (E.C f)⁻¹ (E.W l)) := by
  have hf : E.f f ∈ E.localOrder f := E.base_local _ _
  by_cases e : l=f
  · subst f
    have h : Letter.B.axis ≠ l.axis := by cases l <;> simp_all [Letter.axis]
    obtain ⟨c,k⟩ := E.halfUnits_near h
    rw [W,E.cancel_conjugate]
    exact nearUnit_mul hf k (nearUnit_inv c)
  by_cases t : f=.B
  · subst f
    have h : l.axis ≠ Letter.B.axis := by cases l <;> simp_all [Letter.axis]
    obtain ⟨c,k⟩ := E.halfUnits_near h
    have rev := E.cancel_conjugate .B (E.L l)
    have sw : (commWord (E.L .B) (E.L l))⁻¹=E.W l := by simp [W,commWord,mul_assoc]
    rw [← sw,← conjugate_inv, rev]
    exact nearUnit_inv (nearUnit_mul hf k (nearUnit_inv c))
  · have hbf : Letter.B.axis ≠ f.axis := by cases f <;> simp_all [Letter.axis]
    have hbl : Letter.B.axis ≠ l.axis := by cases l <;> simp_all [Letter.axis]
    obtain ⟨q,hq,_,_,eb,_⟩ := E.split_local hbf false
    have a := screw_comm (E.central f) eb (E.p_commutes hbl false).2.2
      (E.signed_local e false) hq (E.signed_local e true) (E.signed_local (Ne.symm t) true)
    have invO : (↑(E.W l)⁻¹:S) ∈ E.localOrder f := by
      have bb : (E.L .B:S) ∈ E.localOrder f := E.signed_local (Ne.symm t) false
      have aa : (E.L l:S) ∈ E.localOrder f := E.signed_local e false
      have bi : (↑(E.L .B)⁻¹:S) ∈ E.localOrder f := E.signed_local (Ne.symm t) true
      have ai : (↑(E.L l)⁻¹:S) ∈ E.localOrder f := E.signed_local e true
      simpa only [W,commWord,mul_inv_rev,inv_inv,Units.val_mul,mul_assoc] using
        (E.localOrder f).mul_mem bb ((E.localOrder f).mul_mem aa ((E.localOrder f).mul_mem bi ai))
    have hi := near_inverse (x := E.W l) a invO
    have descend (v : Sˣ) (hv : Near (E.localOrder f) (E.f f) 5 (v:S)) :
        Near (E.localOrder f) (E.f f) 1 (conjugate (E.C f)⁻¹ v:S) := by
      obtain ⟨r,hr,ev⟩ := hv
      have hc := E.half_local f
      simpa only [conjugate,Units.val_mul,inv_inv] using
        (half_conjugates (E.central f) hc.1 hc.2.2.1 (Commute.one_left _) ev
          (show (1:S)=1+E.f f*0 by simp) hr (E.localOrder f).zero_mem).2
    exact ⟨descend _ a,by rw [conjugate_inv]; exact descend _ hi⟩

def solution := deepWord (E.W .A) (E.W .A')

theorem solution_integral : (E.solution:S) ∈ E.ι.range ∧ (↑E.solution⁻¹:S) ∈ E.ι.range := by
  have h (f : Letter) : NearUnit (E.localOrder f) (E.f f) 4
      (conjugate (E.C f)⁻¹ E.solution) := by
    have ww := nearUnit_deep (E.base_local f (F f)) (E.central f)
      (E.localW .A (by decide) f) (E.localW .A' (by decide) f)
    simpa only [solution,deepWord,commWord,conjugate_mul,← conjugate_inv] using ww
  constructor
  · apply E.glue
    intro f
    have hh := (h f).1
    simp only [conjugate,Units.val_mul,inv_inv] at hh
    exact unconjugate (E.central f) (E.half_local f).1 (E.half_local f).2.2.1 hh
  · apply E.glue
    intro f
    have hh := (h f).2
    rw [conjugate_inv] at hh
    simp only [conjugate,Units.val_mul,inv_inv] at hh
    exact unconjugate (E.central f) (E.half_local f).1 (E.half_local f).2.2.1 hh

end Ambient
end
end Promislow
