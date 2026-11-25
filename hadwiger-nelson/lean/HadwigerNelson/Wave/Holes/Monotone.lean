import HadwigerNelson.Wave.Holes.Sections

namespace HadwigerNelson.Wave
open MeasureTheory Set
open scoped ENNReal
noncomputable section

private def verticalSection (W : Datum) (u : ℝ) : Set ℝ :=
  {t | |t| ≤ W.y0 ∧ |u| ≤ W.left t}

/-- A vertical section of the hole is a centred interval, allowing a
negative radius for an empty section. -/
private theorem vertical_radius (W : Datum) (u : ℝ) :
    ∃ r : ℝ, ∀ t, t ∈ verticalSection W u ↔ |t| ≤ r := by
  let S := verticalSection W u
  have sym {t : ℝ} (h : t ∈ S) : -t ∈ S := by
    simpa only [S,verticalSection,mem_setOf_eq,abs_neg,W.left_even] using h
  by_cases hn : S.Nonempty
  · have sc : IsCompact S := by
      have e : S = Icc (-W.y0) W.y0 ∩ {t | |u| ≤ W.left t} := by
        ext t; simp [S,verticalSection,abs_le]
      rw [e]
      exact isCompact_Icc.inter_right (isClosed_le continuous_const W.left_continuous)
    obtain ⟨r,hr,hm⟩ := sc.exists_isMaxOn hn (continuousOn_id (s:=S))
    have top {t : ℝ} (h : t ∈ S) : t ≤ r := hm h
    have rn : 0 ≤ r := by linarith [top (sym hr)]
    have rr : r ≤ W.y0 := le_trans (le_abs_self _) hr.1
    refine ⟨r,fun t => ⟨?_,?_⟩⟩
    · intro ht
      exact abs_le.mpr ⟨by linarith [top (sym ht)],top ht⟩
    · intro ht
      have hb : r ≤ H/2 := by linarith [W.y0_bounds.2,H_pos]
      have anti := W.left_antitone ⟨abs_nonneg t, ht.trans hb⟩ ⟨rn,hb⟩ ht
      have he : W.left |t| = W.left t := by
        rcases le_total 0 t with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h,W.left_even]
      exact ⟨ht.trans rr,he ▸ hr.2.trans anti⟩
  · refine ⟨-1,fun t => ⟨fun h => (hn ⟨t,h⟩).elim,fun h => ?_⟩⟩
    linarith [abs_nonneg t]

private theorem vertical_mass (W : Datum) (x y : ℝ) :
    volume (holeOverlap W (point x y)) =
      ∫⁻ u, volume {t : ℝ | t ∈ verticalSection W u ∧ t-y ∈ verticalSection W (u-x)} := by
  have mp := Placement.translationPoint_preserves_volume
  have e := mp.measure_preimage (measurable_holeOverlap W (point x y)).nullMeasurableSet
  rw [←e]
  change (volume.prod volume) (Placement.translationPoint ⁻¹' _) = _
  rw [Measure.prod_apply ((measurable_holeOverlap W _).preimage mp.measurable)]
  rfl

private theorem vertical_mass_mono (W : Datum) (x y y' : ℝ) (h : |y| ≤ |y'|) :
    volume (holeOverlap W (point x y')) ≤ volume (holeOverlap W (point x y)) := by
  rw [vertical_mass,vertical_mass]
  apply lintegral_mono
  intro u
  obtain ⟨a,ha⟩ := vertical_radius W u
  obtain ⟨b,hb⟩ := vertical_radius W (u-x)
  simp only [ha,hb,centred_interval_overlap]
  exact ENNReal.ofReal_le_ofReal (holeSlice_antitone a b h)

theorem holeOverlap_lt_top (W : Datum) (v : Plane) : volume (holeOverlap W v) < ⊤ := by
  let R := (Icc (-1 : ℝ) 1) ×ˢ Icc (-W.y0) W.y0
  have c : IsCompact (Placement.translationPoint '' R) :=
    (isCompact_Icc.prod isCompact_Icc).image Placement.continuous_translationPoint
  apply lt_of_le_of_lt (measure_mono (t:=Placement.translationPoint '' R) ?_) c.measure_lt_top
  intro z hz
  refine ⟨(z 0,z 1),⟨?_,abs_le.mp hz.1.1⟩,?_⟩
  · have h := abs_le.mp (hz.1.2.trans (W.left_bounds _).2.le)
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  · ext i; fin_cases i <;> rfl

theorem holeCovariogram_antitone (W : Datum) (u v : Plane)
    (hx : |u 0| ≤ |v 0|) (hy : |u 1| ≤ |v 1|) :
    holeCovariogram W v ≤ holeCovariogram W u := by
  have ep (z : Plane) : point (z 0) (z 1) = z := by ext i; fin_cases i <;> rfl
  apply ENNReal.toReal_mono (holeOverlap_lt_top W u).ne
  change volume (holeOverlap W v) ≤ volume (holeOverlap W u)
  rw [←ep v,←ep u]
  exact (vertical_mass_mono W _ _ _ hy).trans (horizontal_mass_mono W _ _ _ hx)

end
end HadwigerNelson.Wave
