import HadwigerNelson.Certificate.Hole.Width
import HadwigerNelson.Wave.Holes.Definitions

namespace HadwigerNelson.Certificate.Hole
open Set
noncomputable section

def gridY (dy : ℤ) (i : Fin 69) : ℝ := (gridTick dy i.val:ℝ)/10^12

private def raw (dy : ℤ) (i : ℕ) : ℤ :=
  ((i/2:ℕ):ℤ)*step-cutoff + if i%2=0 then 0 else dy%step

private theorem raw_monotone (dy : ℤ) : Monotone (raw dy) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [raw,step,cutoff]
  split_ifs <;> omega

private theorem grid_mono (dy : ℤ) : Monotone (gridTick dy) := by
  intro i j hij
  apply max_le_max_left
  exact min_le_min_left _ (raw_monotone dy hij)

theorem gridTick_bounds (dy : ℤ) (lo : 0≤dy) (hi : dy<2*cutoff) (i : ℕ) :
    |gridTick dy i|≤cutoff ∧ |gridTick dy i-dy|≤cutoff := by
  have lower : dy-cutoff≤gridTick dy i := le_max_left ..
  have upper : gridTick dy i≤cutoff := max_le (by omega) (min_le_left ..)
  constructor <;> apply abs_le.mpr <;> omega

private theorem proper_cell (dy : ℤ) (i : ℕ) (c : ℤ) (hc : c=0 ∨ c=dy) :
    ∃ j : ℤ, j*step≤raw dy i-c ∧ raw dy (i+1)-c≤(j+1)*step := by
  let q := ((i/2 : ℕ):ℤ)-17
  have dm := Int.emod_add_ediv dy step
  change dy%540000000+540000000*(dy/540000000)=dy at dm
  rcases hc with v | v <;> subst c
  · refine ⟨q,?_⟩
    simp only [q,raw,cutoff,step]
    split_ifs <;> omega
  · by_cases even : i%2=0
    · refine ⟨q-dy/step-1,?_⟩
      simp only [q,raw,cutoff,step,even,if_true]
      split_ifs <;> omega
    · refine ⟨q-dy/step,?_⟩
      simp only [q,raw,cutoff,step,even,if_false]
      split_ifs <;> omega

private theorem clipped_cell (dy : ℤ) (lo : 0≤dy) (hi : dy<2*cutoff) (i : ℕ)
    (h : gridTick dy i < gridTick dy (i+1)) (c : ℤ) (hc : c=0 ∨ c=dy) :
    ∃ j : ℤ, -17 ≤ j ∧ j<17 ∧ j*step≤gridTick dy i-c ∧ gridTick dy (i+1)-c≤(j+1)*step := by
  obtain ⟨j,a,b⟩ := proper_cell dy i c hc
  have l : raw dy i ≤ gridTick dy i := by
    by_cases U : raw dy i ≤ cutoff
    · change raw dy i ≤ max (dy-cutoff) (min cutoff (raw dy i))
      rw [min_eq_right U]; exact le_max_right ..
    · have cap : gridTick dy i = max (dy-cutoff) cutoff := by
        change max _ (min cutoff (raw dy i)) = _
        rw [min_eq_left (le_of_not_ge U)]
      have bound : gridTick dy (i+1) ≤ max (dy-cutoff) cutoff := max_le_max_left _ (min_le_left ..)
      omega
  have r : gridTick dy (i+1) ≤ raw dy (i+1) := by
    by_cases low : dy-cutoff ≤ raw dy (i+1)
    · exact max_le low (min_le_right ..)
    · have eq : gridTick dy (i+1) = dy-cutoff := max_eq_left ((min_le_right ..).trans (le_of_not_ge low))
      have lower : dy-cutoff ≤ gridTick dy i := le_max_left ..
      omega
  have e (n : ℕ) : |gridTick dy n-c|≤cutoff := by
    rcases hc with v | v <;> subst c
    · simpa only [sub_zero] using (gridTick_bounds dy lo hi n).1
    · exact (gridTick_bounds dy lo hi n).2
  have bl := (abs_le.mp (e i)).1
  have br := (abs_le.mp (e (i+1))).2
  refine ⟨j,?_,?_,by omega,by omega⟩ <;> simp only [step,cutoff] at * <;> omega

private theorem affine_of_cell (W : Wave.Datum) (p : Centres.partialProfile W)
    (k : ℕ) (hk : k<17) (sgn : ℝ) (c : ℝ) {l r : ℝ}
    (same : ∀ t∈Icc l r, W.left (sgn*(t-c)) = W.left (t-c))
    (he : ∀ t∈Icc l r, (10^12:ℝ)*(sgn*(t-c))∈Icc ((k:ℝ)*540000000) (((k:ℝ)+1)*540000000)) :
    ∃ a b : ℝ, ∀ t∈Icc l r, W.left (t-c) = a*t+b := by
  let u : ℝ := (PartialWave.leftKnot k).2
  let v : ℝ := (PartialWave.leftKnot (k+1)).2
  refine ⟨(v-u)*sgn/540000000,
    (u-(v-u)*((10^12:ℝ)*sgn*c+(k:ℝ)*540000000)/540000000)/10^12,?_⟩
  intro t ht
  have s := scaled_left_cell p k hk (he t ht)
  rw [show (10^12:ℝ)*(sgn*(t-c))/10^12=sgn*(t-c) by ring,same t ht] at s
  change (10^12:ℝ)*W.left (t-c)=Arithmetic.linearAt _ u _ v _ at s
  rw [Arithmetic.linearAt,show ((k:ℝ)+1)*540000000-k*540000000=540000000 by ring] at s
  linarith only [s]

private theorem affine_cell (W : Wave.Datum) (p : Centres.partialProfile W)
    (l r c j : ℤ) (jm : -17≤j) (jx : j<17) (a : j*step≤l-c) (b : r-c≤(j+1)*step) :
    ∃ A B : ℝ, ∀ t∈Icc ((l:ℝ)/10^12) ((r:ℝ)/10^12), W.left (t-(c:ℝ)/10^12)=A*t+B := by
  have al : (j:ℝ)*540000000≤(l:ℝ)-c := by exact_mod_cast a
  have br : (r:ℝ)-c≤((j:ℝ)+1)*540000000 := by exact_mod_cast b
  by_cases hn : 0≤j
  · let k := j.toNat
    have ek : (k:ℝ)=j := by exact_mod_cast Int.toNat_of_nonneg hn
    apply affine_of_cell W p k (by dsimp [k]; omega) 1
    · simp
    · intro t ht
      rw [ek]
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · let k := (-j-1).toNat
    have ek : (k:ℝ)=-(j:ℝ)-1 := by exact_mod_cast Int.toNat_of_nonneg (show 0≤ -j-1 by omega)
    apply affine_of_cell W p k (by dsimp [k]; omega) (-1)
    · intro t _
      rw [neg_one_mul,W.left_even]
    · intro t ht
      rw [ek]
      exact ⟨by linarith [ht.2],by linarith [ht.1]⟩

theorem grid_partition (W : Wave.Datum) (p : Centres.partialProfile W) (dy : ℤ)
    (lo : 0≤dy) (hi : dy<2*cutoff) : Wave.holePartition W ((dy:ℝ)/10^12) (gridY dy) := by
  have e0 : gridTick dy 0 = dy-cutoff := by
    change max (dy-cutoff) (min cutoff (0-cutoff+0))=_
    omega
  have e68 : gridTick dy 68 = cutoff := by
    change max (dy-cutoff) (min cutoff (34*step-cutoff+0))=_
    simp only [step,cutoff] at *; omega
  refine ⟨?_,?_,?_,?_⟩
  · change (gridTick dy 0:ℝ)/10^12=_
    rw [e0,p.2.1]; push_cast; norm_num [cutoff,step]; ring
  · change (gridTick dy 68:ℝ)/10^12=_
    rw [e68,p.2.1]; norm_num [cutoff,step]
  · intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast grid_mono dy (show i.val≤j.val from hij)) (by norm_num)
  intro i v hv
  obtain ⟨c,hc,hv⟩ : ∃ c : ℤ, (c=0 ∨ c=dy) ∧ v=(c:ℝ)/10^12 := by
    rcases hv with hv | hv
    · exact ⟨0,Or.inl rfl,by simpa using hv⟩
    · exact ⟨dy,Or.inr rfl,hv⟩
  rw [hv]
  have le := grid_mono dy (Nat.le_succ i.val)
  rcases le.eq_or_lt with eq | lt
  · refine ⟨0,W.left (gridY dy i.castSucc - c/10^12),?_⟩
    intro t ht
    have e : gridY dy i.castSucc = gridY dy i.succ := congrArg (fun z : ℤ => (z:ℝ)/10^12) eq
    have et := le_antisymm (ht.2.trans e.ge) ht.1
    rw [et,zero_mul,zero_add]
  · obtain ⟨j,jm,jx,a,b⟩ := clipped_cell dy lo hi i.val lt c hc
    exact affine_cell W p _ _ _ j jm jx a b

end
end HadwigerNelson.Certificate.Hole
