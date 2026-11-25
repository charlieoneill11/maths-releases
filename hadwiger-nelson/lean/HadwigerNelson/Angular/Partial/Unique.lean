import HadwigerNelson.Angular.Partial.Profile

/-! The tabulated interpolants, plateau and periodicity determine the entire
partial wave, including its behaviour outside the fundamental interval. -/

namespace HadwigerNelson.Angular.Partial
open Wave Set

private theorem periodic_ext {f g : ℝ → ℝ} (hf : Function.Periodic f H)
    (hg : Function.Periodic g H) (h : EqOn f g (Icc 0 H)) : f = g := by
  funext x
  let i := ⌊x/H⌋
  have lo := (le_div_iff₀ H_pos).mp (Int.floor_le (x/H))
  have up := (div_lt_iff₀ H_pos).mp (Int.lt_floor_add_one (x/H))
  have cell : x-i*H ∈ Icc 0 H := by dsimp [i]; constructor <;> linarith
  rw [← hf.sub_int_mul_eq i (x := x),← hg.sub_int_mul_eq i (x := x)]
  exact h cell

private theorem grid_eq {n : ℕ} (hn : 0<n) {a : ℝ} (ha : 0<a) {f g : ℝ → ℝ}
    (h : ∀ i : Fin n, ∀ u ∈ Icc (0:ℝ) 1, f (((i:ℝ)+u)*a) = g (((i:ℝ)+u)*a)) :
    EqOn f g (Icc 0 ((n:ℝ)*a)) := by
  intro x hx
  obtain ⟨i,hi,lo,up⟩ := Grid.hasCell hn ⟨div_nonneg hx.1 ha.le,(div_le_iff₀ ha).mpr hx.2⟩
  have eq := h ⟨i,hi⟩ (x/a-i) ⟨by linarith,by linarith⟩
  convert eq using 2 <;> field_simp <;> ring

/-- The concrete periodic datum is the unique wave with these exact profiles
and cutoff. The choice of a periodic extension carries no additional data. -/
theorem Profile.eq_datum {W : Datum} (p : Profile W) (hy : W.y0 = 918/100000) :
    W = PartialWave.datum := by
  have cutoff := hy.trans PartialWave.datum_y0.symm
  have leftLow : EqOn W.left PartialWave.datum.left (Icc 0 ((17:ℝ)*(54/100000))) := by
    apply grid_eq (n:=17) (by decide) (by norm_num)
    intro i u hu
    simpa only [mul_div_assoc] using (p.left i u hu).trans (PartialWave.datum_left_segment i u hu).symm
  have lower {x : ℝ} (hx : x ∈ Icc 0 (H/2)) : W.left x = PartialWave.datum.left x := by
    by_cases early : x ≤ W.y0
    · exact leftLow ⟨hx.1,early.trans (by rw [hy]; norm_num)⟩
    · rw [W.left_zero x ⟨le_of_not_ge early,hx.2⟩,PartialWave.datum.left_zero x ⟨cutoff ▸ (le_of_not_ge early),hx.2⟩]
  have left := periodic_ext W.left_periodic PartialWave.datum.left_periodic (fun {x} hx => by
    by_cases half : x ≤ H/2
    · exact lower ⟨hx.1,half⟩
    · have r := lower (x:=H-x) ⟨sub_nonneg.mpr hx.2,by linarith⟩
      simpa only [W.left_periodic.sub_eq',W.left_even,
        PartialWave.datum.left_periodic.sub_eq',PartialWave.datum.left_even] using r)
  have rightCell : EqOn W.right PartialWave.datum.right (Icc 0 ((512:ℝ)*(H/512))) := by
    apply grid_eq (n:=512) (by decide) (by positivity [H_pos])
    intro i u hu
    simpa only [mul_div_assoc] using (p.right i u hu).trans (PartialWave.datum_right_segment i u hu).symm
  have right := periodic_ext W.right_periodic PartialWave.datum.right_periodic
    (by simpa only [show (512:ℝ)*(H/512)=H by ring] using rightCell)
  have eq_of_fields (a b : Datum) (x : a.x=b.x) (l : a.left=b.left) (r : a.right=b.right)
      (c : a.y0=b.y0) : a=b := by
    cases a; cases b; cases x; cases l; cases r; cases c; rfl
  exact eq_of_fields W PartialWave.datum (p.x.trans PartialWave.datum_x.symm) left right cutoff

end HadwigerNelson.Angular.Partial
