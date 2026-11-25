import HadwigerNelson.Stars.Partial.Classifier
import HadwigerNelson.Stars.PhysicalEnvelope
import HadwigerNelson.Stars.RealFourier

/-! Identification of the three partial-wave columns with the six physical
colour classes, including the nonzero left wall and mirrored row labels. -/
namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (reflected colLift rowLift actualLabel code_iff_residue)
noncomputable section

private theorem unscale (j : Int) (u v : ℝ) :
    InBand j (10^12*u) (10^12*v) ↔
      (j:ℝ)*Wave.H < v ∧ v < ((j:ℝ)+1)*Wave.H ∧
      PartialWave.datum.left v < u ∧ u < PartialWave.datum.right v := by
  have shift : (10^12*v-j*500000000000)/10^12 = v-j*Wave.H := by unfold Wave.H; ring
  simp only [InBand,scaled,shift,PartialWave.datum.left_periodic.sub_int_mul_eq,
    PartialWave.datum.right_periodic.sub_int_mul_eq]
  unfold Wave.H
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem band_iff_copy (c : Nat) (m j : Int) (z : Plane) :
    InBand j (columnX c m (10^12*z 0)) (columnY m (10^12*z 1)) ↔
      Wave.InCopy PartialWave.datum (reflected c) (colLift c m) (rowLift c j) z := by
  let W := PartialWave.datum
  let u := if c≤3 then z 0-2*W.x*m else 2*W.x*m-z 0
  let v := z 1-3/2*Wave.H*m
  have xeq : columnX c m (10^12*z 0)=10^12*u := by
    by_cases hc : c≤3 <;> simp [u,W,columnX,hc,PartialWave.datum_x,PartialWave.xInt] <;> ring
  have yeq : columnY m (10^12*z 1)=10^12*v := by unfold columnY;dsimp [v,Wave.H];ring
  rw [xeq,yeq,unscale]
  by_cases hc : c≤3
  · simp [Wave.InCopy,Wave.localY,Wave.localU,reflected,colLift,rowLift,hc,u,v,W]
  · have ys : Wave.localY true (m-1) z = v+2*Wave.H := by simp [Wave.localY,v]; ring
    have us : Wave.localU W true (m-1) z = u := by simp [Wave.localU,u,hc]
    have perL : W.left (v+2*Wave.H) = W.left v := by simpa using (W.left_periodic.int_mul 2) v
    have perR : W.right (v+2*Wave.H) = W.right v := by simpa using (W.right_periodic.int_mul 2) v
    change _ ↔ Wave.InCopy W _ _ _ _
    simp only [Wave.InCopy,reflected,colLift,rowLift,hc,decide_false,Bool.not_false,if_false,ys,us,
      perL,perR,Int.cast_add,Int.cast_ofNat]
    constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨by linarith,by linarith,c,d⟩

theorem hasCode_iff_colour (c : Nat) (hc : 1≤c ∧ c≤6) (z : Plane) :
    HasCode c (10^12*z 0) (10^12*z 1) ↔ Wave.colour PartialWave.datum z = some (actualLabel c) := by
  rw [Wave.colourClass_iff]
  constructor
  · rintro ⟨m,j,key,mem⟩
    exact ⟨_,_,(code_iff_residue c hc j).1 key,(band_iff_copy c m j z).1 mem⟩
  · rintro ⟨i,k,hl,hh⟩
    let m := if c≤3 then i else i+1
    let j := if c≤3 then k else k-2
    have cm : colLift c m=i := by by_cases h : c≤3 <;> simp [m,colLift,h]
    have rj : rowLift c j=k := by by_cases h : c≤3 <;> simp [j,rowLift,h]
    exact ⟨m,j,(code_iff_residue c hc j).2 (by rwa [rj]),(band_iff_copy c m j z).2
      (by simpa only [cm,rj,actualLabel] using hh)⟩

private theorem classify_decide (b : Angular.Box) (c : Nat) (hc : 1≤c ∧ c≤6) (z : Plane)
    (inside : BoxCheck.InBox b (10^12*z 0) (10^12*z 1))
    (window : -(2*10^12) ≤ 10^12*z 0 ∧ 10^12*z 0 ≤ 2*10^12) :
    BoxCheck.Represents (classify b c) (decide (Wave.colour PartialWave.datum z = some (actualLabel c))) := by
  classical
  obtain ⟨ins,out⟩ := classify_sound b c _ _ inside window
  exact ⟨fun h => decide_eq_true ((hasCode_iff_colour c hc z).1 (ins h)),
    fun h => decide_eq_false (fun e => out h ((hasCode_iff_colour c hc z).2 e))⟩

theorem lowerStep_sound (n a : BoxCheck.Status) (x y : Bool)
    (hn : BoxCheck.Represents n x) (ha : BoxCheck.Represents a y) (dis : ¬(x=true ∧ y=true)) :
    (lowerStep n a).1 ≤ BoxCheck.indicator x-BoxCheck.indicator y := by
  revert hn ha dis
  cases n <;> cases a <;> cases x <;> cases y <;> unfold BoxCheck.Represents <;> decide

/-- Code zero suppresses the alternate label for native-source rectangles. -/
def response (z : Plane) (other : Nat) (θ : ℝ) : ℝ :=
  colourResponse PartialWave.datum z (actualLabel 1) θ -
  (if other=0 then 0 else colourResponse PartialWave.datum z (actualLabel other) θ)

theorem node_lower (src : Angular.Box) (other : Nat)
    (legal : other=0 ∨ (1≤other ∧ other≤6 ∧ actualLabel 1 ≠ actualLabel other))
    (z : Plane) (inside : BoxCheck.InBox src (10^12*z 0) (10^12*z 1)) (xrange : 0≤z 0 ∧ z 0≤1)
    {q a b : Nat} (hq : q<4) (ab : a≤b) (hb : b≤BoxCheck.resolution) {θ : ℝ}
    (hθ : θ∈Set.Icc (BoxCheck.endpoint q a) (BoxCheck.endpoint q b)) :
    ((node src other q a b).1:ℝ) ≤ response z other θ := by
  classical
  let dest := BoxCheck.destination src (BoxCheck.quadrant q (Angular.halfAngleBox BoxCheck.resolution a b))
  let u := z + direction θ
  have hit := BoxCheck.destination_contains inside (BoxCheck.ray_contains hq ab hb hθ)
  have loc : BoxCheck.InBox dest (10^12*u 0) (10^12*u 1) := by
    convert hit using 1 <;> norm_num [direction,u,CompleteWave.scale,mul_add]
  have win : -(2*10^12) ≤ 10^12*u 0 ∧ 10^12*u 0 ≤ 2*10^12 := by
    change -(2*10^12) ≤ 10^12*(z 0+Real.cos θ) ∧ 10^12*(z 0+Real.cos θ) ≤ 2*10^12
    constructor <;> linarith [xrange.1,xrange.2,Real.neg_one_le_cos θ,Real.cos_le_one θ]
  let ev (c : Nat) := decide (Wave.colour PartialWave.datum u = some (actualLabel c))
  have val (c : Nat) : colourResponse PartialWave.datum z (actualLabel c) θ = (BoxCheck.indicator (ev c):ℝ) := by
    by_cases e : Wave.colour PartialWave.datum u = some (actualLabel c) <;>
      simp [colourResponse,labelIndicator,BoxCheck.indicator,ev,u] at e ⊢ <;> simp_all
  have hn : BoxCheck.Represents (classify dest 1) (ev 1) := classify_decide dest 1 (by decide) u loc win
  rcases legal with rfl|⟨l,h,ne⟩
  · have low := lowerStep_sound (classify dest 1) .outside (ev 1) false hn (by simp [BoxCheck.Represents]) (by simp)
    simp only [response,if_pos rfl,sub_zero,val]
    simpa only [node,beq_self_eq_true,if_true,BoxCheck.indicator,Bool.false_eq_true,if_false,sub_zero]
      using (Int.cast_le (R:=ℝ)).mpr low
  · have ha := classify_decide dest other ⟨l,h⟩ u loc win
    have dis : ¬(ev 1=true ∧ ev other=true) := by
      rintro ⟨x,y⟩
      exact ne (Option.some.inj ((of_decide_eq_true x).symm.trans (of_decide_eq_true y)))
    have low := lowerStep_sound _ _ _ _ hn ha dis
    have nz : other≠0 := by omega
    simp only [response,if_neg nz,val]
    simpa only [node,beq_iff_eq,nz,if_false,Int.cast_sub] using (Int.cast_le (R:=ℝ)).mpr low

end
end HadwigerNelson.Stars.PartialCheck
