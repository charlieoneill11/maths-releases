import Promislow.Atoms
import Mathlib.Data.Finsupp.Basic

namespace Promislow
noncomputable section
open MonoidAlgebra

def coord (a : Axis) (g : ElemP) : ℤ := match a with | .x => g.ix | .y => g.iy

def shift (a : Axis) (n : ℤ) : IntegralGroupRing := single (tr a n) 1

def slice (a : Axis) (j : ℤ) (r : IntegralGroupRing) : IntegralGroupRing :=
  Finsupp.filter (fun g => coord a g = j) r

theorem slice_apply (a : Axis) (j : ℤ) (r : IntegralGroupRing) (g : ElemP) :
    slice a j r g = if coord a g = j then r g else 0 := rfl

theorem slice_add (a : Axis) (j : ℤ) (r s : IntegralGroupRing) :
    slice a j (r+s) = slice a j r + slice a j s := by
  ext g; simp only [slice_apply]; split <;> simp_all [slice_apply]

theorem coord_inv_shift (a b : Axis) (n : ℤ) (g : ElemP) :
    coord b ((tr a n)⁻¹ * g) = coord b g - (if a=b then n else 0) := by
  rcases g with ⟨x,y,z,c⟩
  cases a <;> cases b <;> cases c <;>
    simp [coord,tr,show ∀ g h : ElemP, g*h=ElemP.mul g h from fun _ _ => rfl,
      show ∀ g : ElemP, g⁻¹=ElemP.inv g from fun _ => rfl,ElemP.mul,ElemP.inv,
      Coset.mulCocycle,Coset.signX,Coset.signY,Coset.signZ] <;> omega

theorem slice_shift (a b : Axis) (n j : ℤ) (v : IntegralGroupRing) :
    slice b j (shift a n*v) = shift a n * slice b (j - (if a=b then n else 0)) v := by
  ext g
  simp only [shift,slice_apply,single_mul_apply,one_mul,coord_inv_shift]
  split <;> split <;> simp_all

theorem slices_total (a : Axis) (v : IntegralGroupRing) :
    ∑ j ∈ v.support.image (coord a), slice a j v = v := by
  classical
  ext g
  change (∑ j ∈ v.support.image (coord a), slice a j v : ElemP →₀ ℤ) g = _
  rw [Finsupp.finset_sum_apply]
  simp only [slice_apply]
  by_cases h : g ∈ v.support
  · simp [Finset.mem_image_of_mem (coord a) h]
  · simp [Finsupp.notMem_support_iff.mp h]

def shifts (a : Axis) (lags : List ℕ) : IntegralGroupRing :=
  (lags.map (fun n => shift a (n:ℤ))).sum

/-- A monic translation recurrence is injective on a quotient graded by its axis. -/
theorem recurrence (a : Axis) (H : AddSubgroup IntegralGroupRing)
    (sliceH : ∀ j v, v ∈ H → slice a j v ∈ H)
    (shiftH : ∀ n v, v ∈ H → shift a n*v ∈ H)
    (lags : List ℕ) (pos : ∀ n ∈ lags, 0 < n) (v : IntegralGroupRing)
    (h : (1 + shifts a lags)*v ∈ H) : v ∈ H := by
  classical
  let bad := (v.support.image (coord a)).filter (fun j => slice a j v ∉ H)
  have outside (j : ℤ) (hj : j ∉ v.support.image (coord a)) : slice a j v = 0 := by
    ext g
    rw [slice_apply]
    split
    · next hg =>
        have hng : g ∉ v.support := fun h => hj (hg ▸ Finset.mem_image_of_mem (coord a) h)
        simpa using Finsupp.notMem_support_iff.mp hng
    · rfl
  have good (j : ℤ) (hj : j ∉ bad) : slice a j v ∈ H := by
    by_cases hmem : j ∈ v.support.image (coord a)
    · simpa [bad,hmem] using hj
    · rw [outside _ hmem]; exact H.zero_mem
  have empty : ¬ bad.Nonempty := by
    intro hn
    let k := bad.min' hn
    have small (j : ℤ) (hj : j < k) : slice a j v ∈ H :=
      good _ (fun hm => (not_le_of_gt hj) (bad.min'_le j hm))
    have lower (ls : List ℕ) (hp : ∀ n ∈ ls, 0<n) : slice a k (shifts a ls*v) ∈ H := by
      induction ls with
      | nil =>
        have hz : slice a k 0 = 0 := by ext g; simp [slice_apply]
        simp [shifts,hz]
      | cons n ns ih =>
        change slice a k ((shift a (n:ℤ)+shifts a ns)*v) ∈ H
        rw [add_mul,slice_add,slice_shift,if_pos rfl]
        apply H.add_mem
        · apply shiftH
          apply small
          have := hp n (by simp)
          omega
        · exact ih fun m hm => hp m (by simp [hm])
    have both := sliceH k _ h
    rw [add_mul,one_mul,slice_add] at both
    have hk : slice a k v ∈ H := (H.add_mem_cancel_right (lower lags pos)).mp both
    exact (Finset.mem_filter.mp (bad.min'_mem hn)).2 hk
  rw [← slices_total a v]
  exact H.sum_mem fun j _ => good j (fun hj => empty ⟨j,hj⟩)

end
end Promislow
