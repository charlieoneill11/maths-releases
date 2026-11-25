import HadwigerNelson.Centres.MinorArc

/-! On the circle about one center of the rhombus, its open minor arc
is precisely the portion inside the open unit disk about the other center. -/

namespace HadwigerNelson.Centres

theorem minor_disk_iff (p q u v z : Plane) (hpq : p ≠ q) (huv : u ≠ v)
    (hup : dist u p = 1) (huq : dist u q = 1) (hvp : dist v p = 1) (hvq : dist v q = 1)
    (hz : dist z u = 1) : inMinorInterior p q u v z ↔ dist z v < 1 := by
  obtain ⟨_,diag,_⟩ := rhombus_geometry p q u v hpq huv hup huq hvp hvq
  let r := dist v u
  let l := dist p q
  let P := inner ℝ (z-u) (v-u)
  have hr : 0<r := dist_pos.mpr huv.symm
  have hl : 0<l := dist_pos.mpr hpq
  have h₂ : l ≤ 2 := by
    have h := dist_triangle p u q; rw [dist_comm p u,hup,huq] at h
    dsimp [l]; linarith
  have dr : r = Real.sqrt (4-l^2) := (dist_comm v u).trans diag
  have hsq : r^2 = 4-l^2 := dr ▸ Real.sq_sqrt (by nlinarith)
  have hdist := norm_sub_sq_real (z-u) (v-u)
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm,← dist_eq_norm,← dist_eq_norm,hz] at hdist
  change dist z v ^ 2 = 1^2 - 2*P+r^2 at hdist
  have ge : inMinorInterior p q u v z → 0 ≤ P := fun h => h.2.1
  by_cases hs : 0 ≤ P
  · have hx : P/r ≤ 1 := by
      have c := real_inner_le_norm (z-u) (v-u)
      rw [← dist_eq_norm,← dist_eq_norm,hz,one_mul] at c
      exact (div_le_iff₀ hr).mpr (by simpa only [one_mul] using c)
    have lo : -1 ≤ P/r := by linarith [div_nonneg hs hr.le]
    rw [← minor_arc_criterion p q u v z hpq huv hup huq hvp hvq hz hs]
    change Real.arccos (P/r) < Real.arcsin (l/2) ↔ _
    rw [← Real.strictAntiOn_cos.lt_iff_gt
      (show Real.arcsin (l/2) ∈ Set.Icc (0:ℝ) Real.pi from
        ⟨Real.arcsin_nonneg.mpr (by linarith),by linarith [Real.arcsin_le_pi_div_two (l/2),Real.pi_pos]⟩)
      (show Real.arccos (P/r) ∈ Set.Icc (0:ℝ) Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩),
      Real.cos_arcsin,Real.cos_arccos lo hx]
    have s : Real.sqrt (1-(l/2)^2)=r/2 := by
      rw [show 1-(l/2)^2=(r/2)^2 by nlinarith,Real.sqrt_sq (by positivity)]
    rw [s,lt_div_iff₀ hr]
    constructor <;> intro h <;> nlinarith [dist_nonneg (x:=z) (y:=v)]
  · exact iff_of_false (fun h => hs (ge h)) (fun h => hs (by nlinarith [dist_nonneg (x:=z) (y:=v),sq_pos_of_pos hr]))

end HadwigerNelson.Centres
