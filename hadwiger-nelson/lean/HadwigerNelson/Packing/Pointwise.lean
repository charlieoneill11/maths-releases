import HadwigerNelson.Packing.Radial
import HadwigerNelson.Packing.Disks

namespace HadwigerNelson.Packing
open Finset
noncomputable section

theorem near_degree_bound (P : Finset Plane) (z : Plane) (ρ t : ℝ)
    (hρ : 0 < ρ) (ht : 0 < t) (hP : separated P (2*ρ)) (hz : z ∈ P) :
    nearDegree P z t ≤ neighbourCap ρ t := by
  classical
  let S := P.filter fun x ↦ x ≠ z ∧ dist x z ≤ 2*t
  change S.card ≤ _
  have mem {x} (h : x ∈ S) : x ∈ P ∧ x ≠ z ∧ dist x z ≤ 2*t := Finset.mem_filter.mp h
  by_cases small : t ≤ ρ
  · have em : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      have get := mem hx
      have far := hP x get.1 z hz get.2.1
      linarith [get.2.2]
    simp [em]
  let A := ⌊(1+2*t/ρ)^2⌋₊-1
  let M := ⌈100*t/ρ⌉₊
  let U := (M:ℝ)/100
  have zp : z ∉ S := fun h ↦ (mem h).2.1 rfl
  have sub : insert z S ⊆ P := Finset.insert_subset hz (Finset.filter_subset _ _)
  have fallback : S.card ≤ A := by
    have cap := disks (insert z S) z hρ (by linarith : 0 ≤ 2*t)
      (fun x hx y hy hxy ↦ hP x (sub hx) y (sub hy) hxy) (by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl|hx
        · simp; linarith
        · exact (mem hx).2.2)
    have b := Nat.le_floor cap
    rw [Finset.card_insert_of_notMem zp] at b
    dsimp [A]; omega
  have denom : 0 < 2*ρ := by linarith
  let r := fun x ↦ dist x z/(2*ρ)
  have ubd : t/ρ ≤ U := by
    have mc : 100*t/ρ ≤ (M:ℝ) := Nat.le_ceil _
    dsimp [U]; rw [mul_div_assoc] at mc; linarith
  have hU : 0 < U := (div_pos ht hρ).trans_le ubd
  have radii (x) (hx : x ∈ S) : r x ∈ Set.Icc 1 U := by
    have get := mem hx
    refine ⟨(le_div_iff₀ denom).mpr (by linarith [hP x get.1 z hz get.2.1]),?_⟩
    have bound : r x ≤ t/ρ := (div_le_div_iff₀ denom hρ).mpr (by nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr get.2.2)])
    exact bound.trans ubd
  have applyCap (Q : Finset Plane) (hs : Q ⊆ S) (l u : ℝ) (hl : 0<l) (hu : 0<u)
      (rad : ∀ x ∈ Q, r x ∈ Set.Icc l u) : Q.card ≤ annulusCap l u A :=
    annulus_card Q z denom (fun x hx y hy h ↦ hP x (mem (hs hx)).1 y (mem (hs hy)).1 h)
      hl hu rad A ((Finset.card_le_card hs).trans fallback)
  unfold neighbourCap
  dsimp only
  rw [if_neg small]
  apply le_csInf ⟨A,Or.inl rfl⟩
  intro b hb
  rcases hb with eq|eq|⟨j, hj, _, eq⟩
  · exact eq ▸ fallback
  · exact eq ▸ applyCap S (fun _ h ↦ h) _ _ (by norm_num) hU radii
  · let cut := (j:ℝ)/10
    have jpos : 0 < (j:ℝ) := by exact_mod_cast (show 0<j by omega)
    have pos : 0<cut := div_pos jpos (by norm_num)
    let lower := S.filter fun x ↦ r x ≤ cut
    let upper := S.filter fun x ↦ ¬r x ≤ cut
    have low := applyCap lower (Finset.filter_subset _ _) 1 cut (by norm_num) pos (by
      intro x hx; obtain ⟨s,h⟩ := Finset.mem_filter.mp hx
      exact ⟨(radii x s).1,h⟩)
    have high := applyCap upper (Finset.filter_subset _ _) cut U pos hU (by
      intro x hx; obtain ⟨s,h⟩ := Finset.mem_filter.mp hx
      exact ⟨(lt_of_not_ge h).le,(radii x s).2⟩)
    have count : lower.card+upper.card = S.card := Finset.card_filter_add_card_filter_not ..
    rw [eq,← count]
    exact Nat.add_le_add low high

end
end HadwigerNelson.Packing
