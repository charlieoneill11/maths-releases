import ZetaSixth.Regions
import ZetaSixth.SparsePolynomial
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact integration over cells with affine endpoints

The strict inequalities in a cell are used in the geometric partitions. Their open
interval integrals agree with ordered interval integrals because singletons have zero
Lebesgue measure.
-/

namespace ZetaSixth

open MeasureTheory Set

/-- An affine endpoint depending on the first coordinate. -/
structure Affine1 where
  constant : ℚ
  kCoeff : ℚ

namespace Affine1

noncomputable def eval (f : Affine1) (k : ℝ) : ℝ := f.constant + (f.kCoeff : ℝ) * k

def toPoly (f : Affine1) : SparsePoly := [⟨f.constant, ⟨0, 0, 0⟩⟩, ⟨f.kCoeff, ⟨1, 0, 0⟩⟩]

@[simp] theorem eval_toPoly (f : Affine1) (p : Point) :
    f.toPoly.eval p = f.eval p.1 := by
  simp [toPoly, eval, SparseTerm.eval, Powers.eval]

theorem continuous_eval (f : Affine1) : Continuous f.eval := by
  unfold eval
  fun_prop

end Affine1

/-- An affine endpoint depending on the first and second coordinates. -/
structure Affine2 where
  constant : ℚ
  kCoeff : ℚ
  xCoeff : ℚ

namespace Affine2

noncomputable def eval (f : Affine2) (k x : ℝ) : ℝ :=
  f.constant + (f.kCoeff : ℝ) * k + (f.xCoeff : ℝ) * x

def toPoly (f : Affine2) : SparsePoly :=
  [⟨f.constant, ⟨0, 0, 0⟩⟩, ⟨f.kCoeff, ⟨1, 0, 0⟩⟩, ⟨f.xCoeff, ⟨0, 1, 0⟩⟩]

@[simp] theorem eval_toPoly (f : Affine2) (p : Point) :
    f.toPoly.eval p = f.eval p.1 p.2.1 := by
  simp [toPoly, eval, SparseTerm.eval, Powers.eval, add_assoc]

theorem continuous_eval (f : Affine2) : Continuous (fun p : ℝ × ℝ => f.eval p.1 p.2) := by
  unfold eval
  fun_prop

end Affine2

/-- Three nested real intervals with rational affine endpoints, in coordinate order. -/
structure Cell where
  kLo : ℚ
  kHi : ℚ
  xLo : Affine1
  xHi : Affine1
  zLo : Affine2
  zHi : Affine2

namespace Cell

noncomputable def kBand (c : Cell) : Set ℝ := Ioo c.kLo c.kHi

noncomputable def xBand (c : Cell) (k : ℝ) : Set ℝ := Ioo (c.xLo.eval k) (c.xHi.eval k)

noncomputable def zBand (c : Cell) (k x : ℝ) : Set ℝ :=
  Ioo (c.zLo.eval k x) (c.zHi.eval k x)

/-- The open cell defined by the affine faces. -/
noncomputable def set (c : Cell) : Set Point :=
  {p | p.1 ∈ c.kBand ∧ p.2.1 ∈ c.xBand p.1 ∧ p.2.2 ∈ c.zBand p.1 p.2.1}

/-- The upper endpoint is at least the lower endpoint on each relevant fibre. -/
def Ordered (c : Cell) : Prop :=
  (c.kLo : ℝ) ≤ c.kHi ∧ (∀ k ∈ c.kBand, c.xLo.eval k ≤ c.xHi.eval k) ∧
    ∀ k ∈ c.kBand, ∀ x ∈ c.xBand k, c.zLo.eval k x ≤ c.zHi.eval k x

theorem measurableSet_set (c : Cell) : MeasurableSet c.set := by
  apply IsOpen.measurableSet
  have hx : Continuous (fun p : Point => p.2.1) := continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : Point => p.2.2) := continuous_snd.comp continuous_snd
  have hkx : Continuous (fun p : Point => (p.1, p.2.1)) := continuous_fst.prodMk hx
  exact ((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).inter
      (((isOpen_lt (c.xLo.continuous_eval.comp continuous_fst) hx).inter
        (isOpen_lt hx (c.xHi.continuous_eval.comp continuous_fst))).inter
        ((isOpen_lt (c.zLo.continuous_eval.comp hkx) hz).inter
          (isOpen_lt hz (c.zHi.continuous_eval.comp hkx))))

private noncomputable def interpolate (a b t : ℝ) : ℝ := a + t * (b - a)

private theorem exists_interpolate_of_mem_Icc {a b x : ℝ} (hx : x ∈ Icc a b) :
    ∃ t ∈ Icc (0 : ℝ) 1, interpolate a b t = x := by
  rcases lt_or_eq_of_le (hx.1.trans hx.2) with h | rfl
  · have hpos : 0 < b - a := sub_pos.mpr h
    refine ⟨(x - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le, ?_⟩, ?_⟩
    · apply (div_le_iff₀ hpos).2
      simpa only [one_mul] using sub_le_sub_right hx.2 a
    · rw [interpolate, div_mul_cancel₀ _ hpos.ne']
      ring
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa [interpolate] using le_antisymm hx.1 hx.2⟩

private theorem affine_le_on_Icc {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : ∀ t, f (interpolate a b t) = interpolate (f a) (f b) t)
    (hg : ∀ t, g (interpolate a b t) = interpolate (g a) (g b) t)
    (ha : f a ≤ g a) (hb : f b ≤ g b) (hx : x ∈ Icc a b) : f x ≤ g x := by
  obtain ⟨t, ht, rfl⟩ := exists_interpolate_of_mem_Icc hx
  rw [hf, hg, ← sub_nonneg]
  have hdiff : interpolate (g a) (g b) t - interpolate (f a) (f b) t =
      (1 - t) * (g a - f a) + t * (g b - f b) := by
    unfold interpolate
    ring
  rw [hdiff]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha))
    (mul_nonneg ht.1 (sub_nonneg.mpr hb))

/-- Ordering the vertical faces reduces to checking the endpoints of the horizontal faces. -/
theorem ordered_of_corners (c : Cell) (hk : (c.kLo : ℝ) ≤ c.kHi)
    (hxLo : c.xLo.eval c.kLo ≤ c.xHi.eval c.kLo)
    (hxHi : c.xLo.eval c.kHi ≤ c.xHi.eval c.kHi)
    (hzLoLo : c.zLo.eval c.kLo (c.xLo.eval c.kLo) ≤ c.zHi.eval c.kLo (c.xLo.eval c.kLo))
    (hzLoHi : c.zLo.eval c.kLo (c.xHi.eval c.kLo) ≤ c.zHi.eval c.kLo (c.xHi.eval c.kLo))
    (hzHiLo : c.zLo.eval c.kHi (c.xLo.eval c.kHi) ≤ c.zHi.eval c.kHi (c.xLo.eval c.kHi))
    (hzHiHi : c.zLo.eval c.kHi (c.xHi.eval c.kHi) ≤ c.zHi.eval c.kHi (c.xHi.eval c.kHi)) :
    c.Ordered := by
  refine ⟨hk, ?_, ?_⟩
  · intro k hmem
    exact affine_le_on_Icc (by intro t; simp only [Affine1.eval, interpolate]; ring)
      (by intro t; simp only [Affine1.eval, interpolate]; ring) hxLo hxHi
      ⟨hmem.1.le, hmem.2.le⟩
  · intro k hmem x hx
    have hlo : c.zLo.eval k (c.xLo.eval k) ≤ c.zHi.eval k (c.xLo.eval k) :=
      affine_le_on_Icc
        (f := fun b => c.zLo.eval b (c.xLo.eval b)) (g := fun b => c.zHi.eval b (c.xLo.eval b))
        (by intro t; simp only [Affine1.eval, Affine2.eval, interpolate]; ring)
        (by intro t; simp only [Affine1.eval, Affine2.eval, interpolate]; ring) hzLoLo hzHiLo
        ⟨hmem.1.le, hmem.2.le⟩
    have hhi : c.zLo.eval k (c.xHi.eval k) ≤ c.zHi.eval k (c.xHi.eval k) :=
      affine_le_on_Icc
        (f := fun b => c.zLo.eval b (c.xHi.eval b)) (g := fun b => c.zHi.eval b (c.xHi.eval b))
        (by intro t; simp only [Affine1.eval, Affine2.eval, interpolate]; ring)
        (by intro t; simp only [Affine1.eval, Affine2.eval, interpolate]; ring) hzLoHi hzHiHi
        ⟨hmem.1.le, hmem.2.le⟩
    exact affine_le_on_Icc (by intro t; simp only [Affine2.eval, interpolate]; ring)
      (by intro t; simp only [Affine2.eval, interpolate]; ring) hlo hhi ⟨hx.1.le, hx.2.le⟩

private noncomputable def param (c : Cell) (p : Point) : Point :=
  let k := interpolate c.kLo c.kHi p.1
  let x := interpolate (c.xLo.eval k) (c.xHi.eval k) p.2.1
  let z := interpolate (c.zLo.eval k x) (c.zHi.eval k x) p.2.2
  (k, x, z)

private theorem continuous_param (c : Cell) : Continuous c.param := by
  let k : Point → ℝ := fun p => interpolate c.kLo c.kHi p.1
  let x : Point → ℝ := fun p => interpolate (c.xLo.eval (k p)) (c.xHi.eval (k p)) p.2.1
  have hk : Continuous k := by dsimp only [k, interpolate]; fun_prop
  have hxLo := c.xLo.continuous_eval.comp hk
  have hxHi := c.xHi.continuous_eval.comp hk
  have hx : Continuous x := by
    dsimp only [x, interpolate]
    exact hxLo.add ((continuous_fst.comp continuous_snd).mul (hxHi.sub hxLo))
  have hzLo := c.zLo.continuous_eval.comp (hk.prodMk hx)
  have hzHi := c.zHi.continuous_eval.comp (hk.prodMk hx)
  have hz : Continuous (fun p : Point => interpolate (c.zLo.eval (k p) (x p))
      (c.zHi.eval (k p) (x p)) p.2.2) := by
    unfold interpolate
    exact hzLo.add ((continuous_snd.comp continuous_snd).mul (hzHi.sub hzLo))
  exact hk.prodMk (hx.prodMk hz)

theorem integrableOn_eval (c : Cell) (p : SparsePoly) :
    IntegrableOn p.eval c.set := by
  let unitBox : Set Point :=
    Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hc : IsCompact (c.param '' unitBox) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image c.continuous_param
  apply (p.continuous_eval.continuousOn.integrableOn_compact hc).mono_set
  intro q hq
  obtain ⟨s, hs, hsk⟩ := exists_interpolate_of_mem_Icc ⟨hq.1.1.le, hq.1.2.le⟩
  obtain ⟨t, ht, htx⟩ := exists_interpolate_of_mem_Icc ⟨hq.2.1.1.le, hq.2.1.2.le⟩
  obtain ⟨u, hu, huz⟩ := exists_interpolate_of_mem_Icc ⟨hq.2.2.1.le, hq.2.2.2.le⟩
  exact ⟨(s, t, u), ⟨hs, ht, hu⟩, by simp [param, hsk, htx, huz]⟩

private theorem integral_eq_iterated_sets (c : Cell) (p : SparsePoly) :
    ∫ q in c.set, p.eval q =
      ∫ k in c.kBand, ∫ x in c.xBand k, ∫ z in c.zBand k x, p.eval (k, x, z) := by
  let f : Point → ℝ := c.set.indicator p.eval
  have hint : Integrable f (volume.prod volume) :=
    (c.integrableOn_eval p).integrable_indicator c.measurableSet_set
  calc
    ∫ q in c.set, p.eval q = ∫ k : ℝ, ∫ yz : ℝ × ℝ, f (k, yz) := by
      rw [← integral_indicator c.measurableSet_set]
      exact integral_prod f hint
    _ = ∫ k in c.kBand, ∫ x in c.xBand k, ∫ z in c.zBand k x, p.eval (k, x, z) := by
      rw [← integral_indicator (show MeasurableSet c.kBand from measurableSet_Ioo)]
      apply integral_congr_ae
      filter_upwards [hint.prod_right_ae] with k hkint
      by_cases hk : k ∈ c.kBand
      · have hslices : (∫ yz : ℝ × ℝ, f (k, yz)) = ∫ x : ℝ, ∫ z : ℝ, f (k, x, z) :=
          integral_prod _ hkint
        rw [indicator_of_mem hk, hslices,
          ← integral_indicator (show MeasurableSet (c.xBand k) from measurableSet_Ioo)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ c.xBand k
          · rw [indicator_of_mem hx,
              ← integral_indicator (show MeasurableSet (c.zBand k x) from measurableSet_Ioo)]
            dsimp only
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              by_cases hz : z ∈ c.zBand k x
              · have hcell : (k, x, z) ∈ c.set := ⟨hk, hx, hz⟩
                simp only [f, indicator_of_mem hcell, indicator_of_mem hz]
              · have hcell : (k, x, z) ∉ c.set := fun h => hz h.2.2
                simp only [f, indicator_of_notMem hcell, indicator_of_notMem hz]
          · simp [f, set, hx]
      · simp [f, set, hk]

/-- Fubini and the zero measure of interval endpoints identify a cell's set integral with
three ordered interval integrals. -/
theorem integral_eq_iterated (c : Cell) (p : SparsePoly) (h : c.Ordered) :
    ∫ q in c.set, p.eval q =
      ∫ k in (c.kLo : ℝ)..(c.kHi : ℝ),
        ∫ x in c.xLo.eval k..c.xHi.eval k,
          ∫ z in c.zLo.eval k x..c.zHi.eval k x, p.eval (k, x, z) := by
  rw [integral_eq_iterated_sets, intervalIntegral.integral_of_le h.1, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun (show MeasurableSet c.kBand from measurableSet_Ioo)
  intro k hk
  dsimp only
  rw [intervalIntegral.integral_of_le (h.2.1 k hk), integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun (show MeasurableSet (c.xBand k) from measurableSet_Ioo)
  intro x hx
  dsimp only
  rw [intervalIntegral.integral_of_le (h.2.2 k hk x hx), integral_Ioc_eq_integral_Ioo]
  rfl

/-- Evaluate the successively integrated polynomials using rational arithmetic. -/
def integrate (c : Cell) (p : SparsePoly) : ℚ :=
  let pz := p.integrate .third c.zLo.toPoly c.zHi.toPoly
  let px := pz.integrate .second c.xLo.toPoly c.xHi.toPoly
  (px.integrate .first (.const c.kLo) (.const c.kHi)).eval (0, 0, 0)

theorem integrate_eq_iterated (c : Cell) (p : SparsePoly) :
    (c.integrate p : ℝ) =
      ∫ k in (c.kLo : ℝ)..(c.kHi : ℝ),
        ∫ x in c.xLo.eval k..c.xHi.eval k,
          ∫ z in c.zLo.eval k x..c.zHi.eval k x, p.eval (k, x, z) := by
  simp only [integrate, SparsePoly.eval_ratCast, SparsePoly.eval_integrate,
    SparsePoly.eval_const, Affine1.eval_toPoly, Affine2.eval_toPoly, Axis.replace]

/-- Exact rational integration gives the real set integral over an ordered cell. -/
theorem integral_eq (c : Cell) (p : SparsePoly) (h : c.Ordered) :
    (∫ q in c.set, p.eval q) = (c.integrate p : ℝ) :=
  (c.integral_eq_iterated p h).trans (c.integrate_eq_iterated p).symm

end Cell

open SparsePoly in
private def weylDensityPoly (x y z : SparsePoly) : SparsePoly :=
  (const ((Nat.factorial 9 : ℚ) / 4)).mul (((z.sub y).mul (z.sub x)).mul (y.sub x) |>.pow 2)

/-- The density (9! v^2) in the original ((x,y,z)) coordinates. -/
def densityPoly : SparsePoly := weylDensityPoly (.variablePoly .first)
  (.variablePoly .second) (.variablePoly .third)

/-- The density (9! v^2) in the ((k,x,z)) coordinates with (k=x+y). -/
def shortSumDensityPoly : SparsePoly :=
  let k := SparsePoly.variablePoly .first
  let x := SparsePoly.variablePoly .second
  weylDensityPoly x (k.sub x) (.variablePoly .third)

theorem eval_densityPoly (p : Point) :
    densityPoly.eval p = (Nat.factorial 9 : ℝ) * v p ^ 2 := by
  simp [densityPoly, weylDensityPoly, v]
  ring

theorem eval_shortSumDensityPoly (p : Point) :
    shortSumDensityPoly.eval p = (Nat.factorial 9 : ℝ) * v (p.2.1, p.1 - p.2.1, p.2.2) ^ 2 := by
  simp [shortSumDensityPoly, weylDensityPoly, v]
  ring

end ZetaSixth
