import Promislow.Gluing
import Promislow.Letters

namespace Promislow
noncomputable section
open Sparse
variable {S : Type*} [Ring S]

private def fromNorm (d : Sˣ) (cd : ∀ z, Commute (d:S) z) (a b : S)
    (ab : a*b=d) (ba : b*a=d) : Sˣ where
  val := a
  inv := b*↑d⁻¹
  val_inv := by rw [← mul_assoc,ab,Units.mul_inv]
  inv_val := by rw [mul_assoc,((cd a).units_inv_left).eq,← mul_assoc,ba,Units.mul_inv]

namespace Ambient
variable (E : Ambient S)

def den (l : Letter) := E.fu l ^ 4

theorem den_coe (l : Letter) : (E.den l : S) = E.f l ^ 4 := by simp [den]

theorem den_c (l : Letter) (x : S) : Commute (E.den l : S) x :=
  E.den_coe l ▸ (E.central l x).pow_left 4

def C (l : Letter) : Sˣ :=
  fromNorm (E.den l) (E.den_c l) (E.ι (val (firstHalf l))) (E.ι (val (prefixAdj l)))
    (by simpa [den_coe,f] using congrArg E.ι (halfNorm l).1)
    (by simpa [den_coe,f] using congrArg E.ι (halfNorm l).2.1)

def K (l : Letter) : Sˣ :=
  fromNorm (E.den l) (E.den_c l) (E.ι (val (lastHalf l))) (E.ι (val (suffixAdj l)))
    (by simpa [den_coe,f] using congrArg E.ι (halfNorm l).2.2.1)
    (by simpa [den_coe,f] using congrArg E.ι (halfNorm l).2.2.2)

def L (l : Letter) : Sˣ := E.C l * E.K l * (E.den l)⁻¹

def signed (u : Sˣ) (rev : Bool) := if rev then u⁻¹ else u

theorem letter_value (l : Letter) (rev : Bool) :
    ((signed (E.L l) rev : Sˣ) : S) = E.ι (N l rev) * ↑(E.den l)⁻¹ := by
  cases rev
  · change E.ι (val (firstHalf l))*E.ι (val (lastHalf l))*_ = _
    rw [(splitNum l).1,map_mul]
  · change (↑(E.den l):S) * ((E.ι (val (suffixAdj l))*↑(E.den l)⁻¹) *
         (E.ι (val (prefixAdj l))*↑(E.den l)⁻¹)) = _
    rw [(splitNum l).2,map_mul]
    simp only [mul_assoc,(E.den_c l (E.ι (val (suffixAdj l)))).left_comm,Units.mul_inv_cancel_left]

theorem denInv_local {k l : Letter} (h : k≠l) : (↑(E.den k)⁻¹:S) ∈ E.localOrder l := by
  simpa [den,inv_pow] using (E.localOrder l).pow_mem (E.inv_local h) 4

theorem signed_local {k l : Letter} (h : k≠l) (rev : Bool) :
    ((signed (E.L k) rev : Sˣ):S) ∈ E.localOrder l := by
  rw [E.letter_value]
  exact (E.localOrder l).mul_mem (E.base_local _ _) (E.denInv_local h)

theorem half_local (l : Letter) :
    (E.C l : S) ∈ E.localOrder l ∧ (E.K l : S) ∈ E.localOrder l ∧
    E.f l^4*(↑(E.C l)⁻¹:S) ∈ E.localOrder l ∧
    E.f l^4*(↑(E.K l)⁻¹:S) ∈ E.localOrder l := by
  refine ⟨E.base_local _ _,E.base_local _ _,?_,?_⟩
  all_goals
    rw [← E.den_coe]
    change (E.den l:S)*(E.ι _*↑(E.den l)⁻¹) ∈ _
    rw [(E.den_c l _).left_comm,Units.mul_inv,mul_one]
    exact E.base_local _ _

theorem exists_ambient : ∃ (S : Type) (_ : Ring S), Nonempty (Ambient S) := by
  let d := F .A * F .A' * F .B
  have cd (a) : Commute d a := ((centralF .A a).mul_left (centralF .A' a)).mul_left (centralF .B a)
  have reg (a) (h : d*a=0) : a=0 := by
    change (F .A*F .A'*F .B)*a=0 at h
    rw [mul_assoc,mul_assoc] at h
    exact regularF .B _ (regularF .A' _ (regularF .A _ h))
  obtain ⟨S,i,ι,hi,hu,hc⟩ := exists_extension d cd reg
  have hprod : IsUnit ((ι (F .A)*ι (F .A'))*ι (F .B)) := by simpa [d] using hu
  have hh := (((centralF .A (F .B)).map ι).mul_left ((centralF .A' (F .B)).map ι)).isUnit_mul_iff.mp hprod
  have hx := ((centralF .A (F .A')).map ι).isUnit_mul_iff.mp hh.1
  exact ⟨S,i,⟨⟨ι,hi,(fun l => by cases l; exact hx.1; exact hx.2; exact hh.2),
    fun l => hc _ (centralF l)⟩⟩⟩

end Ambient
end
end Promislow
