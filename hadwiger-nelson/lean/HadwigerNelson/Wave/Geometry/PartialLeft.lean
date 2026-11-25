import HadwigerNelson.Wave.Geometry.PartialRight
import Mathlib.Algebra.Order.Group.MinMax

namespace HadwigerNelson.PartialWave
open Wave Angular.Grid
noncomputable section

/-- The first 18 knots are uniformly spaced at 0.00054; the release joins the
last zero to its reflected copy by two flat segments meeting at H/2. -/
def leftStep : ℚ := 540000000 / 1000000000000
def leftOrd (i : Nat) : ℚ := ((leftKnot i).2:ℚ)/1000000000000
def leftArg (y : ℝ) := min 17 (min y (H-y)/(leftStep:ℝ))
def leftAt (y : ℝ) : ℝ := interpolation (fun i => (leftOrd i:ℝ)) 17 (leftArg y)

private theorem physical_step : (leftStep:ℝ)=27/50000 := by norm_num [leftStep]
private theorem step_pos : 0 < (leftStep:ℝ) := by rw [physical_step]; norm_num
private theorem cutoff_eq : cutoff = 17*(leftStep:ℝ) := by rw [physical_step]; norm_num [cutoff]
private theorem cast_left (i : Nat) : (leftOrd i:ℝ) = ((leftKnot i).2:ℝ)/1000000000000 := by simp [leftOrd]

private theorem arg_mem {y : ℝ} (hy : y∈Set.Icc 0 H) : leftArg y ∈ Set.Icc 0 (17:ℝ) :=
  ⟨le_min (by norm_num) (div_nonneg (le_min hy.1 (sub_nonneg.mpr hy.2)) step_pos.le), min_le_left ..⟩

private theorem interpolation_dec : Antitone (interpolation (fun i => (leftOrd i:ℝ)) 17) := by
  apply interpolation_anti
  intro i hi
  have ki := left_knot_ok i (by omega)
  have lo : (leftKnot i).1 < scale/4 := by rw [ki.2.2.1.1 (by omega)]; unfold scale; omega
  rw [cast_left,cast_left]
  exact div_le_div_of_nonneg_right (by exact_mod_cast (ki.2.2.2 (by omega)).2.2.2 lo) (by norm_num)

theorem leftAt_continuous : Continuous leftAt := by
  unfold leftAt leftArg
  apply (interpolation_continuous _ _).comp
  fun_prop

theorem leftAt_reflect (y : ℝ) : leftAt (H-y)=leftAt y := by
  simp only [leftAt,leftArg,sub_sub_cancel,min_comm (H-y) y]

theorem leftAt_antitone : AntitoneOn leftAt (Set.Icc 0 (H/2)) := by
  intro y hy z hz le
  apply interpolation_dec
  unfold leftArg
  rw [min_eq_left (by linarith [hy.2] : y≤H-y),min_eq_left (by linarith [hz.2] : z≤H-z)]
  exact min_le_min_left _ (div_le_div_of_nonneg_right le step_pos.le)

private theorem leftOrd_last : leftOrd 17 = 0 := by
  have : (leftKnot 17).2=0 := by decide +kernel
  simp [leftOrd,this]

private theorem leftAt_flat {y : ℝ} (a : 17*(leftStep:ℝ)≤y) (b : y≤H-17*(leftStep:ℝ)) : leftAt y=0 := by
  have hy : (17:ℝ) ≤ min y (H-y)/leftStep := (le_div_iff₀ step_pos).2 (le_min a (by linarith))
  unfold leftAt leftArg
  rw [min_eq_left hy,show (17:ℝ)=((17:Nat):ℝ) by norm_num,interpolation_right,leftOrd_last]
  norm_num

theorem leftAt_zero (y : ℝ) (hy : y∈Set.Icc cutoff (H/2)) : leftAt y=0 := by
  apply leftAt_flat
  · exact cutoff_eq ▸ hy.1
  · rw [physical_step]; have h := hy.2; unfold H at *; linarith

theorem leftAt_bounds (y : ℝ) (hy : y∈Set.Icc 0 H) : 0 ≤ leftAt y ∧ leftAt y<1/5 := by
  have z := arg_mem hy
  have l := interpolation_dec z.2
  have u := interpolation_dec z.1
  have a : interpolation (fun i => (leftOrd i:ℝ)) 17 0 = leftOrd 0 := by
    rw [interpolation_on _ (show 0<17 by decide) (y:=0) (by norm_num [Set.mem_Icc])]; norm_num
  change (interpolation (fun i => (leftOrd i:ℝ)) 17 (17:ℝ)) ≤ leftAt y at l
  rw [show (17:ℝ)=((17:Nat):ℝ) by norm_num,interpolation_right,leftOrd_last] at l
  rw [a] at u
  have h : (leftKnot 0).2 = 3673765364 := by decide +kernel
  rw [cast_left,h] at u
  constructor
  · simpa using l
  · change leftAt y ≤ _ at u
    linarith

theorem leftAt_lipschitz (y z : ℝ) (hy : y∈Set.Icc 0 H) (hz : z∈Set.Icc 0 H) :
    |leftAt y-leftAt z| ≤ |y-z| := by
  have slope (i : Nat) (hi : i<17) : |(leftOrd (i+1):ℝ)-(leftOrd i:ℝ)|≤leftStep := by
    have a := left_knot_ok i (by omega)
    have b := left_knot_ok (i+1) (by omega)
    obtain ⟨_,lo,up,_⟩ := a.2.2.2 (by omega)
    rw [a.2.2.1.1 (by omega),b.2.2.1.1 (by omega)] at lo up
    have l : ((leftKnot (i+1)).2:ℝ)+i*540000000 ≤ (leftKnot i).2+((i:ℝ)+1)*540000000 := by exact_mod_cast lo
    have u : ((leftKnot i).2:ℝ)+i*540000000 ≤ (leftKnot (i+1)).2+((i:ℝ)+1)*540000000 := by exact_mod_cast up
    rw [cast_left,cast_left,abs_le,physical_step]
    constructor <;> linarith
  have mm := abs_min_sub_min_le_max y (H-y) z (H-z)
  rw [show H-y-(H-z)= -(y-z) by ring,abs_neg,max_self] at mm
  have clamp := abs_min_sub_min_le_max (17:ℝ) (min y (H-y)/leftStep) 17 (min z (H-z)/leftStep)
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg _),← sub_div,abs_div,abs_of_pos step_pos] at clamp
  have h := interpolation_lipschitz (fun i => (leftOrd i:ℝ)) 17 (by decide) (leftStep:ℝ) slope (arg_mem hy) (arg_mem hz)
  change |leftArg y-leftArg z| ≤ _ at clamp
  unfold leftAt
  exact h.trans ((le_of_eq (mul_comm _ _)).trans (((le_div_iff₀ step_pos).mp clamp).trans mm))

private def segment (i : Nat) : ℚ × ℚ × ℚ × ℚ :=
  ((i:ℚ)*leftStep,((i:ℚ)+1)*leftStep,(leftOrd (i+1)-leftOrd i)/leftStep,
    leftOrd i-(leftOrd (i+1)-leftOrd i)*i)
private def reflected (p : ℚ × ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (1/2-p.2.1,1/2-p.1,-p.2.2.1,p.2.2.1/2+p.2.2.2)
private def flat : ℚ × ℚ × ℚ × ℚ := (17*leftStep,1/2-17*leftStep,0,0)

private theorem segment_formula (i : Nat) (hi : i<17) {z : ℝ}
    (hz : z∈Set.Icc ((segment i).1:ℝ) ((segment i).2.1:ℝ)) :
    leftAt z=((segment i).2.2.1:ℝ)*z+(segment i).2.2.2 := by
  change (((i:ℚ)*leftStep:ℚ):ℝ) ≤ z ∧ z ≤ ((((i:ℚ)+1)*leftStep:ℚ):ℝ) at hz
  push_cast at hz
  have cap : (i:ℝ)+1 ≤ 17 := by exact_mod_cast (show i+1≤17 by omega)
  have hcap := hz.2.trans (mul_le_mul_of_nonneg_right cap step_pos.le)
  have low : z≤H-z := by rw [physical_step] at hcap; unfold H; linarith
  have a := (le_div_iff₀ step_pos).2 hz.1
  have b := (div_le_iff₀ step_pos).2 hz.2
  unfold leftAt leftArg
  rw [min_eq_left low,min_eq_right (b.trans cap),interpolation_on _ hi ⟨a,b⟩]
  dsimp [segment]; push_cast; ring

theorem leftAt_rational : RationalProfile leftAt := by
  classical
  let pieces := (Finset.range 17).image segment
  refine ⟨insert flat (pieces ∪ pieces.image reflected),fun y hy => ?_⟩
  have pick (t : ℝ) (h0 : 0≤t) (h1 : t≤17*(leftStep:ℝ)) :
      ∃ i<17,t∈Set.Icc ((segment i).1:ℝ) ((segment i).2.1:ℝ) := by
    obtain ⟨i,hi,ha,hb⟩ := hasCell (n:=17) (by decide) (show t/leftStep∈Set.Icc 0 (17:ℝ) from
      ⟨div_nonneg h0 step_pos.le,(div_le_iff₀ step_pos).2 h1⟩)
    refine ⟨i,hi,?_⟩
    dsimp [segment]; push_cast
    exact ⟨(le_div_iff₀ step_pos).mp ha,(div_le_iff₀ step_pos).mp hb⟩
  by_cases low : y ≤ 17*(leftStep:ℝ)
  · obtain ⟨i,hi,h⟩ := pick y hy.1 low
    refine ⟨segment i,Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩)),h,fun z _ hz => segment_formula i hi hz⟩
  by_cases high : H-y≤17*(leftStep:ℝ)
  · obtain ⟨i,hi,h⟩ := pick (H-y) (sub_nonneg.mpr hy.2) high
    let p := segment i
    refine ⟨reflected p,Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨p,Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩,rfl⟩)),?_,?_⟩
    · change H-y ∈ Set.Icc (p.1:ℝ) (p.2.1:ℝ) at h
      rcases h with ⟨a,b⟩
      dsimp [reflected]; push_cast; unfold H at a b; constructor <;> linarith
    · intro z _ hz
      change (((1/2-p.2.1):ℚ):ℝ) ≤ z ∧ z ≤ (((1/2-p.1):ℚ):ℝ) at hz
      push_cast at hz; obtain ⟨a,b⟩ := hz
      have hh : H-z∈Set.Icc (p.1:ℝ) (p.2.1:ℝ) := by unfold H; constructor <;> linarith
      have l := segment_formula i hi hh
      rw [leftAt_reflect] at l
      change leftAt z=(p.2.2.1:ℝ)*(H-z)+p.2.2.2 at l
      rw [l]; dsimp [reflected]; push_cast; unfold H; ring
  · refine ⟨flat,Finset.mem_insert_self ..,?_,?_⟩
    · dsimp [flat]; push_cast; unfold H at high; constructor <;> linarith
    · intro z _ hz
      have hz' : 17*(leftStep:ℝ)≤z ∧ z≤H-17*(leftStep:ℝ) := by simpa [flat,H] using hz
      rw [leftAt_flat hz'.1 hz'.2]; simp [flat]

end
end HadwigerNelson.PartialWave
