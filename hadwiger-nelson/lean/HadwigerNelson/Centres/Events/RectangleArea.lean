import HadwigerNelson.Centres.Events.Measurable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace HadwigerNelson.Centres
open MeasureTheory Set
open scoped ENNReal Function
noncomputable section

private def box (h lo hi : ℝ) : Set Plane :=
  {z | |z 0| < h ∧ z 1 ∈ Ioo lo hi}

private theorem box_open (h lo hi : ℝ) : IsOpen (box h lo hi) := by
  exact (isOpen_lt ((PiLp.continuous_apply 2 _ 0).abs) continuous_const).inter
    (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 1))

private theorem box_volume (h lo hi : ℝ) :
    volume (box h lo hi) = ENNReal.ofReal (2*h)*ENNReal.ofReal (hi-lo) := by
  let a : Fin 2 → ℝ := ![-h,lo]
  let b : Fin 2 → ℝ := ![h,hi]
  let S := univ.pi fun i => Ioo (a i) (b i)
  have ms : MeasurableSet S := MeasurableSet.pi countable_univ (fun _ _ => measurableSet_Ioo)
  have eq : box h lo hi = (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' S := by
    ext z
    change (|z 0|<h ∧ z 1∈Ioo lo hi) ↔ ∀ i∈(univ : Set (Fin 2)), z i∈Ioo (a i) (b i)
    rw [abs_lt]
    constructor
    · rintro ⟨x,y⟩ i _
      fin_cases i
      · exact x
      · exact y
    · intro p
      exact ⟨p 0 trivial,p 1 trivial⟩
  rw [eq,(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage ms.nullMeasurableSet,Real.volume_pi_Ioo,
    Fin.prod_univ_two]
  simp [a,b,two_mul]

private def low (dy : ℝ) (j : Nat) (neg : Bool) := if neg then -((j+1:Nat)*dy) else j*dy
private def high (dy : ℝ) (j : Nat) (neg : Bool) := if neg then -(j*dy) else (j+1:Nat)*dy

private theorem coordinate {dy z : ℝ} (hd : 0<dy) (j : Nat) (neg : Bool)
    (h : z ∈ Ioo (low dy j neg) (high dy j neg)) :
    (j:ℝ)*dy < |z| ∧ |z| < ((j:ℝ)+1)*dy ∧ (z<0 ↔ neg=true) := by
  have jn : 0≤(j:ℝ)*dy := by positivity
  rcases h with ⟨a,b⟩
  cases neg
  · simp only [low,high,Bool.false_eq_true,if_false,Nat.cast_add,Nat.cast_one] at a b
    have pos := jn.trans_lt a
    rw [abs_of_pos pos]
    exact ⟨a,b,iff_of_false (not_lt.mpr pos.le) Bool.false_ne_true⟩
  · simp only [low,high,if_true,Nat.cast_add,Nat.cast_one] at a b
    have s : z<0 := by linarith
    rw [abs_of_neg s]
    exact ⟨by linarith,by linarith,iff_of_true s rfl⟩

theorem halfWidth_nonneg (W : Wave.Datum) (p : Profile) (l : ℝ) (i k : Nat) :
    0 ≤ rectangleHalfWidth W p l i k := le_max_left ..

private theorem width_bounded (W : Wave.Datum) (y : ℝ) : width W y ≤ 1/5 := by
  unfold width
  split
  · exact (W.left_bounds _).2.le
  · norm_num

theorem region_bounds (W : Wave.Datum) (p : Profile) (l t : ℝ) (step : 0≤angleStep p l)
    {z : Plane} (hz : z ∈ smallRegion W p l t) : |z 0|≤1/5 ∧ |z 1|≤Wave.H/4 := by
  rcases hz with ⟨k,x,_,y⟩
  have hx (i k : ℕ) : rectangleHalfWidth W p l i k ≤ 1/5 := by
    unfold rectangleHalfWidth
    apply max_le (by norm_num)
    apply (min_le_left ..).trans
    exact (sub_le_self _ (by positivity)).trans (width_bounded W _)
  refine ⟨x.le.trans (hx _ _),?_⟩
  have dk : ((k.val:ℝ)+1)≤heightBins p := by exact_mod_cast k.isLt
  have n : 0 < heightBins p := by cases p <;> decide
  have ds : 0≤heightStep p := by unfold heightStep; positivity
  have hy := mul_le_mul_of_nonneg_right dk ds
  have endY : (heightBins p : ℝ)*heightStep p = 9/1000 := by unfold heightStep; field_simp
  rw [endY] at hy
  unfold Wave.H
  linarith

theorem smallRegion_measurable (W : Wave.Datum) (p : Profile) (l t : ℝ) :
    MeasurableSet (smallRegion W p l t) := by
  unfold smallRegion
  rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro k
  exact (isOpen_lt (PiLp.continuous_apply 2 _ 0).abs continuous_const).measurableSet.inter
    ((PiLp.continuous_apply 2 _ 1).abs.measurable measurableSet_Icc)

theorem smallRegion_area (W : Wave.Datum) (p : Profile) (l t : ℝ) (step : 0≤angleStep p l) :
    4*heightStep p * (∑ k : Fin (heightBins p), rectangleHalfWidth W p l (angleBin p l t) k.val) ≤
      volume.real (smallRegion W p l t) := by
  let dy := heightStep p
  let M := heightBins p
  let h (k : Fin M) := rectangleHalfWidth W p l (angleBin p l t) k.val
  let B (v : Fin M × Bool) := box (h v.1) (low dy v.1.val v.2) (high dy v.1.val v.2)
  have nd : 0<heightBins p := by cases p <;> decide
  have hd : 0<dy := by dsimp [dy,heightStep]; positivity
  have dis : Pairwise (Disjoint on B) := by
    intro ⟨i,ni⟩ ⟨j,nj⟩ ne
    apply disjoint_left.mpr
    intro z a b
    obtain ⟨ai,bi,ci⟩ := coordinate hd i.val ni a.2
    obtain ⟨aj,bj,cj⟩ := coordinate hd j.val nj b.2
    have indices : i=j := by
      apply Fin.ext
      by_contra bad
      rcases lt_or_gt_of_ne bad with lt|gt
      · have e : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast lt
        linarith [mul_le_mul_of_nonneg_right e hd.le]
      · have e : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast gt
        linarith [mul_le_mul_of_nonneg_right e hd.le]
    apply ne
    apply Prod.ext indices
    cases ni <;> cases nj <;> tauto
  have sub : (⋃ v, B v) ⊆ smallRegion W p l t := by
    rintro z hz
    obtain ⟨⟨k,neg⟩,hz⟩ := mem_iUnion.mp hz
    obtain ⟨a,b,_⟩ := coordinate hd k.val neg hz.2
    refine ⟨k,hz.1,a.le,?_⟩
    dsimp only [dy] at b
    linarith
  have area (v : Fin M × Bool) : volume.real (B v) = 2*h v.1*dy := by
    have h' : 0≤ h v.1 := halfWidth_nonneg ..
    have eq : high dy v.1.val v.2 - low dy v.1.val v.2 =dy := by
      rcases v with ⟨j,c⟩
      cases c <;> simp [high,low] <;> ring
    change (volume (box (h v.1) (low dy v.1.val v.2) (high dy v.1.val v.2))).toReal = _
    rw [box_volume,eq,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal hd.le]
  have finite : volume (smallRegion W p l t) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (box 1 (-1) 1)) ?_ (measure_mono ?_)
    · rw [box_volume]; finiteness
    · intro z hz
      have ⟨a,b⟩ := region_bounds W p l t step hz
      change |z 0| < 1 ∧ -1 < z 1 ∧ z 1 < 1
      obtain ⟨bl,br⟩ := abs_le.mp b
      unfold Wave.H at bl br
      exact ⟨by linarith,by linarith,by linarith⟩
  have est := measureReal_mono (μ:=volume) sub finite
  rw [measureReal_iUnion_fintype dis (fun v => (box_open ..).measurableSet)
    (fun v => by dsimp only [B]; rw [box_volume]; finiteness)] at est
  simp_rw [area] at est
  rw [Fintype.sum_prod_type] at est
  simp only [Fintype.sum_bool] at est
  refine (le_of_eq ?_).trans est
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [h,dy]
  ring

end
end HadwigerNelson.Centres
