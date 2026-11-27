import Promislow.Factors
import Promislow.Localization

namespace Promislow
noncomputable section

theorem bezoutF : (F .A - 1)*F .A - F .A' = 1 := by
  unfold F
  let p := Sparse.factor .A
  let q := Sparse.factor .A'
  change (Sparse.val p - 1)*Sparse.val p - Sparse.val q = 1
  have h : Sparse.val (Sparse.mul p p) = Sparse.val (Sparse.add Sparse.one (Sparse.add q p)) :=
    congrArg Sparse.val (by decide +kernel)
  simp only [Sparse.val_mul,Sparse.val_add,Sparse.val_one] at h
  rw [sub_mul,one_mul,h]
  abel

private theorem bezout_mem {S : Type*} [Ring S] (O : Subring S) (a b : S)
    (ha : a ∈ O) (hb : b ∈ O) (ab : Commute a b) (bez : (a-1)*a-b=1)
    (n m : ℕ) (q : S) (x : a^n*q ∈ O) (y : b^m*q ∈ O) : q∈O := by
  have step (r : S) (ar : a*r∈O) (br : b*r∈O) : r∈O := by
    have hh := O.sub_mem (O.mul_mem (O.sub_mem ha O.one_mem) ar) br
    rwa [← mul_assoc,← sub_mul,bez,one_mul] at hh
  have single (k : ℕ) (r : S) (ar : a*r∈O) (br : b^k*r∈O) : r∈O := by
    induction k generalizing r with
    | zero => simpa using br
    | succ k ih =>
      apply step r ar
      apply ih
      · rw [ab.left_comm]; exact O.mul_mem hb ar
      · simpa [pow_succ,mul_assoc] using br
  induction n generalizing q with
  | zero => simpa using x
  | succ n ih =>
    apply single m q _ y
    apply ih (a*q)
    · simpa [pow_succ,mul_assoc] using x
    · rw [(ab.pow_right m).symm.left_comm]
      exact O.mul_mem ha y

/-- The global fraction ring only needs to invert the product of the three factors. -/
structure Ambient (S : Type*) [Ring S] where
  ι : IntegralGroupRing →+* S
  inj : Function.Injective ι
  unitF : ∀ f, IsUnit (ι (F f))
  central : ∀ f, ∀ x, Commute (ι (F f)) x

namespace Ambient
variable {S : Type*} [Ring S] (E : Ambient S)

def f (l : Letter) : S := E.ι (F l)
def fu (l : Letter) : Sˣ := (E.unitF l).unit
@[simp] theorem coe_fu (l : Letter) : (E.fu l : S) = E.f l := IsUnit.unit_spec _

def others : Letter → Letter × Letter
  | .A => (.A',.B) | .A' => (.A,.B) | .B => (.A,.A')

def outside (l : Letter) := E.f (others l).1 * E.f (others l).2

theorem outside_central (l : Letter) (x : S) : Commute (E.outside l) x :=
  (E.central _ x).mul_left (E.central _ x)

def localOrder (l : Letter) : Subring S :=
  over E.ι (E.outside l) (E.outside_central l)
    (E.ι.range.mul_mem ⟨F _,rfl⟩ ⟨F _,rfl⟩)

theorem base_local (l : Letter) (r : IntegralGroupRing) : E.ι r ∈ E.localOrder l :=
  over_base E.ι r

theorem inv_local {k l : Letter} (h : k ≠ l) : (↑(E.fu k)⁻¹:S) ∈ E.localOrder l := by
  refine ⟨1,?_⟩
  rw [pow_one]
  have either : k=(others l).1 ∨ k=(others l).2 := by cases k <;> cases l <;> simp_all [others]
  have swap : Commute (E.f (others l).1) (E.f (others l).2) := E.central _ _
  obtain hk | hk := either
  · rw [hk,outside, swap.eq, mul_assoc, ← E.coe_fu (others l).1, Units.mul_inv,mul_one]
    exact ⟨_, rfl⟩
  · rw [hk,outside,mul_assoc,← E.coe_fu (others l).2,Units.mul_inv,mul_one]
    exact ⟨_,rfl⟩

theorem glue (q : S) (hq : ∀ f, q ∈ E.localOrder f) : q ∈ E.ι.range := by
  let a := E.f .A
  let b := E.f .A'
  let c := E.f .B
  let O := over E.ι c (E.central .B) (show c ∈ E.ι.range from ⟨_,rfl⟩)
  obtain ⟨n,hn⟩ := hq .A
  obtain ⟨m,hm⟩ := hq .A'
  change (b*c)^n*q ∈ E.ι.range at hn
  change (a*c)^m*q ∈ E.ι.range at hm
  have sep (t : S) (ct : Commute c t) (k : ℕ) (hh : (t*c)^k*q ∈ E.ι.range) : t^k*q ∈ O := by
    refine ⟨k,?_⟩
    rwa [← mul_assoc, ← ct.mul_pow,ct.eq]
  have hbez : (a-1)*a-b=1 := by simpa [a,b,f] using congrArg E.ι bezoutF
  have hO := bezout_mem O a b (over_base E.ι (F .A)) (over_base E.ι (F .A'))
    (E.central .A b) hbez m n q (sep _ (E.central .B a) _ hm) (sep _ (E.central .B b) _ hn)
  obtain ⟨j,s,hs⟩ := hO
  obtain ⟨k,r,hr⟩ := hq .B
  let D := (F .A*F .A')^k
  have hr' : E.ι r = E.ι D*q := by simpa [D, outside, others, f] using hr
  change E.ι s = c^j*q at hs
  have cen (z : IntegralGroupRing) : Commute D z :=
    ((centralF .A z).mul_left (centralF .A' z)).pow_left k
  have HD : D ∈ preserves .y :=
    (preserves .y).pow_mem ((preserves .y).mul_mem (factor_preserves .A) (factor_preserves .A')) k
  have heq : F .B ^ j * r = D*s := by
    apply E.inj
    rw [map_mul,map_pow,hr',map_mul,hs]
    exact ((E.central .B (E.ι D)).pow_left j).left_comm q
  have peel (i : ℕ) (z : IntegralGroupRing) (hz : F .B ^ i*z ∈ multiples D) : z∈multiples D := by
    induction i generalizing z with
    | zero => simpa using hz
    | succ i ih =>
      apply cancel_factor .B D HD cen
      apply ih
      simpa [pow_succ,mul_assoc] using hz
  obtain ⟨z,hz⟩ := peel j r ⟨s,heq⟩
  refine ⟨z,?_⟩
  have u : IsUnit (E.ι D) := by
    simpa [D] using ((E.unitF .A).mul (E.unitF .A')).pow k
  apply u.mul_left_cancel
  rw [← map_mul,← hz,hr']

end Ambient
end
end Promislow
