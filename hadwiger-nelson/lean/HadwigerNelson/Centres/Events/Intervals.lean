import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Centres.Events.Runtime
import Mathlib.Tactic.IntervalCases

namespace HadwigerNelson.Centres.Quadrature
open Set

noncomputable section

structure SmallMatch (p : Profile) (l : ℝ) (s : Small) : Prop where
  lo : (s.lower:ℝ) = smallLower p l
  hi : (s.upper:ℝ) = smallUpper p l
  n : s.angles = angleBins p
  m : s.heights = heightBins p
  intercept : (s.target:ℝ) = if δ≤l then Centres.intercept p else smallIntercept p

private theorem coarse_ne_fine : Profile.coarse ≠ Profile.fine := by decide
private theorem fine_ne_coarse : Profile.fine ≠ Profile.coarse := by decide

theorem small_match (p : Profile) (l : ℝ) :
    ∃ k : Fin 6, SmallMatch p l (small k.val) := by
  cases p with
  | coarse =>
    by_cases large : δ ≤ l
    · refine ⟨1,?_⟩
      constructor <;> norm_num [coarse_ne_fine,fine_ne_coarse,small,smallLower,smallUpper,angleBins,heightBins,Centres.intercept,smallIntercept,
        delta,δ,large,not_lt.mpr large] <;> norm_num [δ] at * <;> (try split_ifs) <;> simp_all <;> linarith
    · refine ⟨0,?_⟩
      constructor <;> norm_num [coarse_ne_fine,fine_ne_coarse,small,smallLower,smallUpper,angleBins,heightBins,Centres.intercept,smallIntercept,
        deltaR,δR,large,lt_of_not_ge large] <;> norm_num [δ] at * <;> (try split_ifs) <;> simp_all <;> linarith
  | fine =>
    by_cases large : δ ≤ l
    · have above : ¬l≤6/1000 := by dsimp [δ] at large; linarith
      by_cases eight : l≤8/1000
      · refine ⟨4,?_⟩
        constructor <;> norm_num [coarse_ne_fine,fine_ne_coarse,small,smallLower,smallUpper,angleBins,heightBins,Centres.intercept,smallIntercept,
          large,not_lt.mpr large,above,eight,not_lt.mpr eight,delta,δ] <;> norm_num [δ] at * <;> (try split_ifs) <;> simp_all <;> linarith
      · refine ⟨5,?_⟩
        constructor <;> norm_num [coarse_ne_fine,fine_ne_coarse,small,smallLower,smallUpper,angleBins,heightBins,Centres.intercept,smallIntercept,
          large,not_lt.mpr large,above,eight,lt_of_not_ge eight] <;> norm_num [δ] at * <;> (try split_ifs) <;> simp_all <;> linarith
    · by_cases six : l≤6/1000
      · refine ⟨2,?_⟩
        constructor <;> norm_num [coarse_ne_fine,fine_ne_coarse,small,smallLower,smallUpper,angleBins,heightBins,Centres.intercept,smallIntercept,
          large,lt_of_not_ge large,six,not_lt.mpr six,deltaR,δR] <;> norm_num [δ] at * <;> (try split_ifs) <;> simp_all <;> linarith
      · refine ⟨3,?_⟩
        constructor <;> norm_num [coarse_ne_fine,fine_ne_coarse,small,smallLower,smallUpper,angleBins,heightBins,Centres.intercept,smallIntercept,
          large,lt_of_not_ge large,six,lt_of_not_ge six] <;> norm_num [δ] at * <;> (try split_ifs) <;> simp_all <;> linarith


theorem SmallMatch.dt_eq {p : Profile} {l : ℝ} {s : Small} (h : SmallMatch p l s)
    (smallChord : l≤2/100) : (s.dt:ℝ) = angleStep p l := by
  simp [Small.dt,angleStep,cone,if_pos smallChord,h.lo,h.n]

theorem SmallMatch.dy_eq {p : Profile} {l : ℝ} {s : Small} (h : SmallMatch p l s) :
    (s.dy:ℝ) = heightStep p := by simp [Small.dy,heightStep,h.m]

theorem breakpoint_strict : StrictMono breakpoint := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases early : i<6
  · interval_cases i <;> norm_num [breakpoint]
  · let k := i-6
    have e : i = k+6 := by dsimp [k]; omega
    rw [e]
    change (190+(k:ℚ))/1000 < (190+((k+1:ℕ):ℚ))/1000
    push_cast; linarith

theorem breakpoint_mem {b : ℝ} :
    b ∈ mediumBreaks ↔ ∃ i : Fin 62, (breakpoint i.val : ℝ) = b := by
  classical
  unfold mediumBreaks
  rw [Finset.mem_union]
  constructor
  · rintro (first|tail)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at first
      rcases first with rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨0,by norm_num [breakpoint]⟩
      · exact ⟨1,by norm_num [breakpoint]⟩
      · exact ⟨2,by norm_num [breakpoint]⟩
      · exact ⟨3,by norm_num [breakpoint]⟩
      · exact ⟨4,by norm_num [breakpoint]⟩
      · exact ⟨5,by norm_num [breakpoint]⟩
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp tail
      have lt := Finset.mem_range.mp hk
      exact ⟨⟨k+6,by omega⟩,by simp [breakpoint]⟩
  · rintro ⟨i,rfl⟩
    by_cases early : i.val<6
    · left
      let n := i.val
      change ((breakpoint n:ℚ):ℝ) ∈ _
      change n<6 at early
      interval_cases n <;> norm_num [breakpoint]
    · right
      let k := i.val-6
      have kk : i.val=k+6 := by dsimp [k]; omega
      apply Finset.mem_image.mpr
      refine ⟨k,Finset.mem_range.mpr (by dsimp [k]; omega),?_⟩
      rw [kk]
      simp [breakpoint]

theorem medium_interval {l : ℝ} (lo : 2/100 < l) (hi : l≤245/1000) :
    ∃ i : Fin 61, (breakpoint i.val:ℝ)<l ∧ l≤(breakpoint (i.val+1):ℝ) := by
  let P (k : Nat) := l ≤ (breakpoint k:ℝ)
  have endpoint : P 61 := by norm_num [P,breakpoint] at *; linarith
  have existsK : ∃ k, P k := ⟨61,endpoint⟩
  let k := Nat.find existsK
  have bound : k≤61 := Nat.find_min' existsK endpoint
  have nz : k≠0 := by intro h; have := Nat.find_spec existsK; change P k at this; rw [h] at this; norm_num [P,breakpoint] at this; linarith
  let i := k-1
  have ik : i+1=k := by dsimp [i]; omega
  refine ⟨⟨i,by omega⟩,?_,?_⟩
  · exact lt_of_not_ge (Nat.find_min existsK (show i<k by omega))
  · change P (i+1)
    rw [ik]
    exact Nat.find_spec existsK

theorem medium_cone (p : Profile) {l : ℝ} {i : Fin 61} (above : 2/100<l)
    (a : (breakpoint i.val:ℝ)<l) (b : l≤(breakpoint (i.val+1):ℝ)) :
    cone p l = (mEnd (breakpoint i.val) : ℝ) := by
  have member : (breakpoint i.val:ℝ) ∈ {t | t∈mediumBreaks ∧ t<l} :=
    ⟨breakpoint_mem.mpr ⟨⟨i.val,by omega⟩,rfl⟩,a⟩
  have greatest : IsGreatest {t | t∈mediumBreaks ∧ t<l} (breakpoint i.val:ℝ) := by
    refine ⟨member,?_⟩
    rintro t ⟨hm,lt⟩
    obtain ⟨j,rfl⟩ := breakpoint_mem.mp hm
    have hlt : breakpoint j.val < breakpoint (i.val+1) := by exact_mod_cast lt.trans_le b
    have idx := breakpoint_strict.lt_iff_lt.mp hlt
    have le : j.val ≤ i.val := Nat.le_of_lt_succ idx
    exact_mod_cast (breakpoint_strict.monotone le)
  rw [cone,if_neg (not_le.mpr above),greatest.csSup_eq]
  norm_num [mEnd,unitCone,w]

end
end HadwigerNelson.Centres.Quadrature
