import HadwigerNelson.Stars.BoxFamilies
import HadwigerNelson.Stars.RowSound

/-! Physical source coordinates, colour labels and angular gain for the complete wave. -/

namespace HadwigerNelson.Stars.BoxCheck
noncomputable section

private theorem source_alternate (i : Nat) :
    (source i).other = 4 ∨ (source i).other = 2 ∨ (source i).other = 6 := by
  by_cases first : i < 1200
  · left; simp only [source, if_pos first]; rfl
  by_cases second : i < 4464
  · right; left; simp only [source, if_neg first, if_pos second]; rfl
  · right; right; simp only [source, if_neg first, if_neg second]; rfl

private theorem alternate_ok (c : Nat) (hc : c=4 ∨ c=2 ∨ c=6) :
    (1 ≤ c ∧ c ≤ 6) ∧ actualLabel 1 ≠ actualLabel c := by
  rcases hc with rfl | rfl | rfl <;> decide

private theorem centre_data (s : Source) {z : Plane} (hz : z ∈ physicalSource s)
    (subset : physicalSource s ⊆ Wave.halfTile Wave.completeDatum false) :
    Wave.colour Wave.completeDatum z = some (actualLabel 1) ∧ 0 ≤ z 0 ∧ z 0 ≤ 1 := by
  have tile : z ∈ Wave.tile Wave.completeDatum := (subset hz).1
  have zr := (Placement.tile_coord_bounds _ tile).1
  exact ⟨Placement.colour_on_tile _ _ tile,zr.1.le,zr.2.le⟩

private theorem response_domain (s : Source) {z : Plane} (inside : z ∈ physicalSource s)
    (half : physicalSource s ⊆ Wave.halfTile Wave.completeDatum false)
    (codes : s.other=4 ∨ s.other=2 ∨ s.other=6) :
    ResponseDomain s.box s.other z ∧ Wave.colour Wave.completeDatum z = some (actualLabel 1) := by
  have ⟨lohi, different⟩ := alternate_ok _ codes
  have ⟨centre, xrange⟩ := centre_data s inside half
  exact ⟨⟨lohi, different, source_in_box inside, xrange⟩, centre⟩

theorem harmonic_response_domain (pass : checkSourceBoxes = true) (i : Fin 14464)
    {z : Plane} (inside : z ∈ physicalSource (source i.val)) :
    ResponseDomain (source i.val).box (source i.val).other z ∧
      Wave.colour Wave.completeDatum z = some (actualLabel 1) :=
  response_domain _ inside (physical_source_half i ((checkSourceBoxes_spec pass).1 i)) (source_alternate i)

theorem saturated_response_domain (pass : checkSourceBoxes = true) (i : Fin 252)
    {z : Plane} (inside : z ∈ physicalSource (saturated i.val)) :
    ResponseDomain (saturated i.val).box (saturated i.val).other z ∧
      Wave.colour Wave.completeDatum z = some (actualLabel 1) :=
  response_domain _ inside (physical_saturated_half i ((checkSourceBoxes_spec pass).2 i)) (Or.inl rfl)

private theorem harmonic_gain_of_row {d : ℕ} (hd : 0<d) (k : Fin harmonics)
    (φ : Fin d → ℝ) (i : Fin 14464) (z : Plane)
    (native : Wave.colour Wave.completeDatum z = some (actualLabel 1))
    (mean : meanValue (moments arcTable (source i.val)) ≤
      angleMean (physicalSigned z (source i.val).other))
    (coeff : magnitudeValue k.val (moments arcTable (source i.val)) ≤
      ‖angleMoment (k.val+1) (physicalSigned z (source i.val).other)‖) :
    (d:ℝ)/2 * harmonicLocal k φ i ≤ angularGain Wave.completeDatum φ z :=
  real_fourier_star_bound hd _ φ z _ _ native (k.val+1) _ _ mean coeff

private theorem saturated_gain_of_row {d : ℕ} (hd : 0<d)
    (φ : Fin d → ℝ) (i : Fin 252) (z : Plane)
    (native : Wave.colour Wave.completeDatum z = some (actualLabel 1))
    (mean : (nativeFraction arcTable (saturated i.val) : ℝ)/quant ≤ angleMean (physicalNative z)) :
    (d:ℝ) * saturatedLocal d i ≤ angularGain Wave.completeDatum φ z :=
  real_native_star_bound hd _ φ z _ native _ mean

theorem row_mean_lower (s : Source) {z : Plane} (dom : ResponseDomain s.box s.other z) :
    meanValue (moments arcTable s) ≤ angleMean (physicalSigned z s.other) := by
  let M := spanSum ((runs s.box s.other).map (prepareSpan arcTable)) SpanMoments.mean
  change (normalise M 4 : ℝ)/quant ≤ _
  have raw : (M : ℝ) ≤ _ := signed_mean_ticks dom
  have norm := normalise_sound M 4 (by decide)
  push_cast at norm
  apply norm.trans
  rw [angleMean_eq_interval]
  have S : (0:ℝ)<phaseScale := by norm_num [phaseScale]
  apply (div_le_div_of_nonneg_right raw (show 0≤4*(phaseScale:ℝ)*Real.pi by positivity)).trans_eq
  field_simp
  ring

theorem native_fraction_lower (s : Source) {z : Plane} (dom : ResponseDomain s.box s.other z) :
    (nativeFraction arcTable s : ℝ)/quant ≤ angleMean (physicalNative z) := by
  let M := nativeTicks arcTable (runs s.box s.other)
  change (normalise M 2 : ℝ)/quant ≤ _
  have raw : (M : ℝ) ≤ _ := native_mean_ticks dom
  have norm := normalise_sound M 2 (by decide)
  push_cast at norm
  apply norm.trans
  rw [angleMean_eq_interval]
  have S : (0:ℝ)<phaseScale := by norm_num [phaseScale]
  apply (div_le_div_of_nonneg_right raw (show 0≤2*(phaseScale:ℝ)*Real.pi by positivity)).trans_eq
  field_simp

/-- Every saturated source gives the same-colour contribution at each of its points. -/
theorem saturated_source_gain (pass : checkSourceBoxes = true) {d : ℕ} (hd : 0<d)
    (φ : Fin d → ℝ) (i : Fin 252) (z : Plane) (inside : z ∈ physicalSource (saturated i.val)) :
    (d:ℝ) * saturatedLocal d i ≤ angularGain Wave.completeDatum φ z := by
  obtain ⟨dom,native⟩ := saturated_response_domain pass i inside
  exact saturated_gain_of_row hd φ i z native (native_fraction_lower _ dom)

/-- Each of the 14,464 Fourier sources satisfies its rounded row estimate
for the actual star at every point of its physical interior. -/
theorem harmonic_source_gain (pass : checkSourceBoxes = true) {d : ℕ} (hd : 0<d)
    (k : Fin harmonics) (φ : Fin d → ℝ) (i : Fin 14464) (z : Plane)
    (inside : z ∈ physicalSource (source i.val)) :
    (d:ℝ)/2 * harmonicLocal k φ i ≤ angularGain Wave.completeDatum φ z := by
  obtain ⟨dom,native⟩ := harmonic_response_domain pass i inside
  exact harmonic_gain_of_row hd k φ i z native (row_mean_lower _ dom)
    (row_magnitude_lower k _ dom)

end
end HadwigerNelson.Stars.BoxCheck
