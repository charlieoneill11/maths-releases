import HadwigerNelson.Centres.CandidateMetric
import HadwigerNelson.Centres.Events.Definitions

/-! The exact enclosure supplied by the rectangle containing an event
midpoint, with its clamped angular index and height band. -/

namespace HadwigerNelson.Centres
noncomputable section
open Set

theorem small_levels (p : Profile) {l : ℝ} (lo : δR≤l) (hi : l≤2/100) :
    0<smallLower p l ∧ smallLower p l≤l ∧ l≤smallUpper p l ∧ smallUpper p l≤2/100 := by
  cases p <;> unfold smallLower smallUpper <;>
    split_ifs <;> norm_num [δR,δ] at * <;> grind

private theorem grid_tick {x c : ℝ} {n : ℕ} (hc : 0<c) (hn : 0<n) (hx : x≤c) :
    let d := c/n
    let k := max 1 (min n ⌈x/d⌉₊)
    x ≤ (k:ℝ)*d ∧ (k:ℝ)*d ≤ c := by
  let d := c/n
  have dn : 0<d := div_pos hc (Nat.cast_pos.mpr hn)
  have nd : (n:ℝ)*d=c := by dsimp [d]; field_simp
  have kmax : ⌈x/d⌉₊ ≤ n := Nat.ceil_le.mpr ((div_le_iff₀ dn).mpr (nd ▸ hx))
  dsimp only
  rw [min_eq_right kmax]
  change x≤(max 1 ⌈x/d⌉₊ : ℕ)*d ∧ (max 1 ⌈x/d⌉₊ : ℕ)*d ≤ c
  have kg : (⌈x/d⌉₊:ℝ) ≤ (max 1 ⌈x/d⌉₊ : ℕ) := by exact_mod_cast le_max_right 1 _
  have kl : ((max 1 ⌈x/d⌉₊ : ℕ):ℝ) ≤ n := by exact_mod_cast max_le hn kmax
  exact ⟨(div_le_iff₀ dn).mp ((Nat.le_ceil _).trans kg), (mul_le_mul_of_nonneg_right kl dn.le).trans_eq nd⟩

structure SmallCell (W : Wave.Datum) (p : Profile) (l t : ℝ) (M : Plane) where
  y : ℝ
  dy : ℝ
  tick : ℝ
  a : ℝ
  b : ℝ
  y_nonneg : 0≤y
  y_upper : y+dy ≤ 9/1000
  tick_lower : |t|≤tick
  tick_upper : tick≤365/100000
  a_eq : a=1-Real.sqrt (1-(smallUpper p l)^2/4)+tick^2/2
  a_nonneg : 0≤a
  b_eq : b=a+w^2/2
  b_upper : b≤1/1000
  ordinate : |M 1| ∈ Icc y (y+dy)
  first_width : |M 0|+tick < width W (y+dy+a)
  second_width : width W (max 0 (y-b))+|M 0|+b*tick < smallLower p l/2

theorem smallCell_exists (W : Wave.Datum) (p : Profile) {l t : ℝ} {M : Plane}
    (lo : δR≤l) (hi : l≤2/100) (ht : |t|≤cone p l) (mem : M∈smallRegion W p l t) :
    Nonempty (SmallCell W p l t M) := by
  let N : ℕ := if p=.coarse then 32 else 100
  let K : ℕ := if p=.coarse then 48 else 180
  let d := cone p l/N
  let dy := (9/1000:ℝ)/K
  let i := max 1 (min N ⌈|t|/d⌉₊)
  let tick := (i:ℝ)*d
  let a := 1-Real.sqrt (1-(smallUpper p l)^2/4)+tick^2/2
  let b := a+w^2/2
  obtain ⟨k,both⟩ := mem
  let y := (k.val:ℝ)*dy
  change |M 0| < max 0 (min (width W (y+dy+a)-tick) (smallLower p l/2-width W (max 0 (y-b))-b*tick)) ∧
    |M 1| ∈ Icc y (y+dy) at both
  obtain ⟨dx,fy⟩ := both
  have parts := lt_min_iff.mp ((lt_max_iff.mp dx).resolve_left (not_lt_of_ge (abs_nonneg _)))
  have levels := small_levels p lo hi
  have hn : 0<N := by dsimp [N]; split <;> decide
  have hk : 0<K := by dsimp [K]; split <;> decide
  have con : 0<cone p l := by rw [cone,if_pos hi]; exact lt_min (by norm_num) (half_pos levels.1)
  have ticks := grid_tick con hn ht
  change |t| ≤ tick ∧ tick ≤ cone p l at ticks
  have t0 := (abs_nonneg t).trans ticks.1
  have tmax := ticks.2.trans (cone_small p l)
  have ua : (smallUpper p l)^2 ≤ (2/100:ℝ)^2 :=
    pow_le_pow_left₀ (levels.1.le.trans (levels.2.1.trans levels.2.2.1)) levels.2.2.2 2
  have s₂ := Real.sq_sqrt (show 0≤1-(smallUpper p l)^2/4 by linarith)
  have spos := Real.sqrt_nonneg (1-(smallUpper p l)^2/4)
  have slow : 9999/10000 ≤ Real.sqrt (1-(smallUpper p l)^2/4) := by
    apply (sq_le_sq₀ (by norm_num) spos).mp; nlinarith only [s₂,ua]
  have shi : Real.sqrt (1-(smallUpper p l)^2/4) ≤ 1 := by
    apply (sq_le_sq₀ spos zero_le_one).mp; nlinarith only [s₂,sq_nonneg (smallUpper p l)]
  have dy0 : 0≤dy := by dsimp [dy]; positivity
  have limit : y+dy≤9/1000 := by
    have kreal : (k.val:ℝ)+1 ≤ K := by exact_mod_cast k.isLt
    have eq : (K:ℝ)*dy=9/1000 := by dsimp [dy]; field_simp
    dsimp only [y]
    linarith [mul_le_mul_of_nonneg_right kreal dy0]
  refine ⟨⟨y,dy,tick,a,b,mul_nonneg (Nat.cast_nonneg _) dy0,limit,ticks.1,tmax,rfl,
    by dsimp [a]; linarith [sq_nonneg tick],rfl,?_,fy,by linarith [parts.1],by linarith [parts.2]⟩⟩
  dsimp only [b,a,w]
  nlinarith [pow_le_pow_left₀ t0 tmax 2]

end
end HadwigerNelson.Centres
