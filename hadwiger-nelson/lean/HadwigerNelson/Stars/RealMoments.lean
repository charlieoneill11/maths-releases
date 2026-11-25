import HadwigerNelson.Stars.PhysicalEnvelope
import HadwigerNelson.Stars.ArcWeights
import HadwigerNelson.Stars.RealFourier
import HadwigerNelson.Stars.RealFourier.Primitive
import HadwigerNelson.Stars.RealFourier.SpanBounds

/-! Certified integral inequalities for the physical responses over a full turn.
The centre can lie anywhere inside the source rectangle. -/

namespace HadwigerNelson.Stars.BoxCheck
open MeasureTheory Set
open CompleteWave (scale)
noncomputable section

structure ResponseDomain (src : Angular.Box) (other : Nat) (z : Plane) : Prop where
  colourRange : 1 ≤ other ∧ other ≤ 6
  distinct : actualLabel 1 ≠ actualLabel other
  inside : InBox src (scale*z 0) (scale*z 1)
  xrange : 0 ≤ z 0 ∧ z 0 ≤ 1

abbrev physicalSigned (z : Plane) (other : Nat) :=
  signedResponse Wave.completeDatum z (actualLabel 1) (actualLabel other)

abbrev physicalNative (z : Plane) := colourResponse Wave.completeDatum z (actualLabel 1)

private theorem spanEnvelope {src : Angular.Box} {other : Nat} {z : Plane}
    (dom : ResponseDomain src other z) {q a b : Nat} (hq : q < 4) (hab : a ≤ b)
    (hb : b ≤ resolution) {θ : ℝ} (hθ : θ ∈ Ioo (endpoint q a) (endpoint q b)) :
    let s := nodeSpan src other q a b
    |2 * physicalSigned z other θ-s.coeff| ≤ s.radius :=
  node_envelope src other dom.colourRange dom.distinct z dom.inside dom.xrange hq hab hb
    ⟨hθ.1.le,hθ.2.le⟩

private theorem integral_sub_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ∀ a b, IntervalIntegrable f volume a b) (a b : ℝ) :
    (∫ t in 0..b, f t) - (∫ t in 0..a, f t) = ∫ t in a..b, f t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf 0 a) (hf a b)]
  abel

private theorem scale_pos : (0 : ℝ) < phaseScale := by norm_num [phaseScale]

theorem signed_mean_ticks {src : Angular.Box} {other : Nat} {z : Plane}
    (dom : ResponseDomain src other z) :
    (spanSum ((runs src other).map (prepareSpan arcTable)) SpanMoments.mean : ℝ) ≤
      2*(phaseScale : ℝ)*(∫ θ in 0..2*Real.pi, physicalSigned z other θ) := by
  let g := physicalSigned z other
  have hi (a b : ℝ) : IntervalIntegrable g volume a b := intervalIntegrable_signedResponse _ _ _ _ _ _
  let G (t : ℝ) := 2*(phaseScale : ℝ)*(∫ θ in 0..t, g θ)
  rw [meanWeight_ticks]
  have out := fullTurn_lower src other meanWeight G (by
    intro q hq a b hab hb
    let s := nodeSpan src other q a b
    have loc := span_mean_lower (fun θ => 2*g θ) (m := (s.coeff : ℝ)) (r := (s.radius : ℝ))
      (endpoint_monotone q hab.le) ((hi _ _).const_mul 2) (fun θ hθ => by
        have w := spanEnvelope dom hq hab.le hb hθ
        change |2*g θ-(s.coeff:ℝ)| ≤ s.radius at w
        linarith only [(abs_le.mp w).1] )
    rw [intervalIntegral.integral_const_mul] at loc
    have lo := meanWeight_bound s hab.le hb
    change changeOf meanWeight s ≤ G (endpoint q b)-G (endpoint q a)
    dsimp only [G]
    rw [←mul_sub, integral_sub_prefix g hi]
    calc
      _ ≤ (phaseScale:ℝ)*(((s.coeff:ℝ)-s.radius)*(endpoint q b-endpoint q a)) := by
        change changeOf meanWeight s ≤ (phaseScale:ℝ)*((s.coeff:ℝ)-s.radius)*
          (endpoint q b-endpoint q a) at lo
        rwa [mul_assoc] at lo
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left loc scale_pos.le])
  simpa only [G,intervalIntegral.integral_same,mul_zero,sub_zero] using out

theorem native_mean_ticks {src : Angular.Box} {other : Nat} {z : Plane}
    (dom : ResponseDomain src other z) :
    (nativeTicks arcTable (runs src other) : ℝ) ≤
      (phaseScale : ℝ)*(∫ θ in 0..2*Real.pi, physicalNative z θ) := by
  let f := physicalNative z
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := intervalIntegrable_colourResponse _ _ _ _ _
  let G (t : ℝ) := (phaseScale : ℝ)*(∫ θ in 0..t, f θ)
  rw [nativeWeight_ticks]
  have out := fullTurn_lower src other nativeWeight G (by
    intro q hq a b hab hb
    let s := nodeSpan src other q a b
    change changeOf nativeWeight s ≤ G (endpoint q b)-G (endpoint q a)
    dsimp only [G]
    rw [←mul_sub, integral_sub_prefix f hi]
    have htime := endpoint_monotone q hab.le
    by_cases status : s.coeff == 2 && s.radius == 0
    · have cr := status
      simp only [Bool.and_eq_true,beq_iff_eq] at cr
      obtain ⟨c,r⟩ := cr
      have loc := span_mean_lower f (m := 1) (r := 0) htime (hi _ _) (fun θ hθ => by
        have w := spanEnvelope dom hq hab.le hb hθ
        change |2*physicalSigned z other θ-(s.coeff:ℝ)| ≤ s.radius at w
        rw [c,r] at w
        have nonneg : 0 ≤ colourResponse Wave.completeDatum z (actualLabel other) θ := by
          unfold colourResponse labelIndicator; split <;> norm_num
        change 1-0 ≤ physicalNative z θ
        change |2*(physicalNative z θ-colourResponse Wave.completeDatum z (actualLabel other) θ)-_| ≤ _ at w
        norm_num only [Int.cast_ofNat,Int.cast_zero] at w
        linarith only [(abs_le.mp w).1,nonneg])
      simp only [sub_zero,one_mul] at loc
      simp only [changeOf,nativeWeight,status,if_true]
      exact (arc_low_high q a b hab.le hb).1.trans (mul_le_mul_of_nonneg_left loc scale_pos.le)
    · simp [changeOf,nativeWeight,status]
      apply mul_nonneg scale_pos.le
      apply intervalIntegral.integral_nonneg htime
      intro θ _
      dsimp [f,physicalNative,colourResponse,labelIndicator]
      split <;> norm_num)
  simpa only [G,intervalIntegral.integral_same,mul_zero,sub_zero] using out

/-- The primitive of the midpoint response on a constant envelope. -/
private def harmonicWeight (k q : Nat) (c _ : Int) (i : Nat) : ℂ :=
  -(Complex.I/(k:ℂ))*(c:ℂ)*exactPhase q i^k

private theorem harmonicWeight_eval (spans : Array Span) (k : Nat) :
    spanEval spans (changeOf (harmonicWeight k)) =
      Complex.I/(k:ℂ)*spanEval spans (fun p => exactTerm p k) := by
  rw [spanEval_fin,spanEval_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [changeOf,harmonicWeight,exactTerm]
  ring

theorem signed_moment_ticks {src : Angular.Box} {other : Nat} {z : Plane}
    (dom : ResponseDomain src other z) (k : Nat) (hk : 0 < k) :
    ‖(∫ θ in 0..2*Real.pi, ((2*physicalSigned z other θ : ℝ):ℂ)*anglePhase θ^k) -
      Complex.I/(k:ℂ)*spanEval (runs src other) (fun p => exactTerm p k)‖ ≤
      (spanSum ((runs src other).map (prepareSpan arcTable)) SpanMoments.error:ℝ)/phaseScale := by
  let g (θ : ℝ) := 2*physicalSigned z other θ
  let h (θ : ℝ) := (g θ:ℂ)*anglePhase θ^k
  have gi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (intervalIntegrable_signedResponse _ _ _ _ _ _).const_mul 2
  have hi (a b : ℝ) : IntervalIntegrable h volume a b := by
    have ic : IntervalIntegrable (fun θ => (g θ : ℂ)) volume a b :=
      ⟨(gi a b).1.ofReal,(gi a b).2.ofReal⟩
    exact ic.mul_continuousOn (anglePhase_continuous.pow k).continuousOn
  let G (t : ℝ) := ∫ θ in 0..t, h θ
  have out := fullTurn_error src other (harmonicWeight k) errorWeight G (by
    intro q hq a b hab hb
    let s := nodeSpan src other q a b
    have loc := span_moment_error_le g k (m := (s.coeff:ℝ)) (r := (s.radius:ℝ))
      (endpoint_monotone q hab.le) (gi _ _) (fun θ hθ => spanEnvelope dom hq hab.le hb hθ)
    have weight : changeOf (harmonicWeight k) s =
        ((s.coeff:ℝ):ℂ)*(∫ θ in endpoint q a..endpoint q b, anglePhase θ^k) := by
      rw [integral_anglePhase_pow _ _ _ hk, endpoint_phase q a hq, endpoint_phase q b hq]
      change _-_ = _
      change -(Complex.I/(k:ℂ))*(s.coeff:ℂ)*exactPhase q b^k -
        (-(Complex.I/(k:ℂ))*(s.coeff:ℂ)*exactPhase q a^k) = _
      push_cast
      ring
    change ‖G (endpoint q b)-G (endpoint q a)-changeOf (harmonicWeight k) s‖ ≤ changeOf errorWeight s
    dsimp only [G]
    rw [integral_sub_prefix h hi,weight]
    exact loc.trans (errorWeight_bound s hab.le hb (radius_nonneg ..)))
  rw [←errorWeight_ticks, harmonicWeight_eval] at out
  simpa only [G, intervalIntegral.integral_same,sub_zero] using out

end
end HadwigerNelson.Stars.BoxCheck
