import Chowla.VariationalApproximation
import Chowla.Model.WickLabels

namespace Chowla

open Filter MeasureTheory MvPolynomial
open scoped BigOperators Topology

/-- Bounds and integral convergence for a sequence of Fourier profiles. -/
structure ProfileConverges (F : ℕ → FourierProfile) (f : FourierProfile) : Prop where
  profile : IsProfile f
  profiles : ∀ n, IsProfile (F n)
  bounded : ∃ M R : ℝ, 0 ≤ M ∧ HasRadiusAtMost f R ∧
    (∀ n u, |F n u| ≤ M) ∧ (∀ n, HasRadiusAtMost (F n) R)
  l1 : Tendsto (fun n => profileL1 (F n - f)) atTop (𝓝 0)

private theorem integrable_convolve_integrand {f g : FourierProfile} (hf : Integrable f)
    (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (u : ℝ) :
    Integrable (fun t => f t * g (u - t)) := by
  apply hf.mul_bdd ((hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun t => hM (u - t)

theorem profileConverges_convolve {F G : ℕ → FourierProfile} {f g : FourierProfile}
    (hf : ProfileConverges F f) (hg : ProfileConverges G g) :
    ProfileConverges (fun n => convolve (F n) (G n)) (convolve f g) := by
  have hfi := integrable_of_isProfile hf.profile
  have hgi := integrable_of_isProfile hg.profile
  have hFi n := integrable_of_isProfile (hf.profiles n)
  have hGi n := integrable_of_isProfile (hg.profiles n)
  refine ⟨convolve_isProfile hf.profile hg.profile,
    fun n => convolve_isProfile (hf.profiles n) (hg.profiles n), ?_,
    profileL1_convolve_tendsto hfi hgi hFi hGi hf.l1 hg.l1⟩
  obtain ⟨M₁, R₁, hM₁, hR₁, hMb₁, hRb₁⟩ := hf.bounded
  obtain ⟨M₂, R₂, hM₂, hR₂, hMb₂, hRb₂⟩ := hg.bounded
  refine ⟨(M₁ * (2 * R₁)) * M₂, R₁ + R₂, (by have := hR₁.1; positivity), convolve_hasRadiusAtMost hR₁ hR₂,
    ?_, fun n => convolve_hasRadiusAtMost (hRb₁ n) (hRb₂ n)⟩
  intro n u
  refine (abs_convolve_le_of_right_bound (hFi n) (hMb₂ n) u).trans
    (mul_le_mul_of_nonneg_right ?_ hM₂)
  let A := Set.Icc (-R₁) R₁
  have hA : Integrable (A.indicator (fun _ => M₁) : ℝ → ℝ) :=
    (integrableOn_const (measure_Icc_lt_top.ne : volume A ≠ ⊤)).integrable_indicator measurableSet_Icc
  have hb : ∀ᵐ u : ℝ ∂volume, |F n u| ≤ A.indicator (fun _ => M₁) u := by
    filter_upwards [(hRb₁ n).2] with x hx
    by_cases he : x ∈ A
    · simpa [he] using hMb₁ n x
    · simp [he, hx he]
  unfold profileL1
  calc
    _ ≤ ∫ u : ℝ, A.indicator (fun _ => M₁) u := integral_mono_ae (hFi n).abs hA hb
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith [hR₁.1])]
      ring

theorem profileConverges_convolve_tendsto_at {F G : ℕ → FourierProfile} {f g : FourierProfile}
    (hf : ProfileConverges F f) (hg : ProfileConverges G g) (u : ℝ) :
    Tendsto (fun n => convolve (F n) (G n) u) atTop (𝓝 (convolve f g u)) := by
  obtain ⟨M, _, _, _, hG, _⟩ := hg.bounded
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hf.profile.2.2.1
  have hb (t : ℝ) : |f t| ≤ B := hB _ ⟨t, rfl⟩
  have hfi := integrable_of_isProfile hf.profile
  have hgi := integrable_of_isProfile hg.profile
  have hFi n := integrable_of_isProfile (hf.profiles n)
  have hGi n := integrable_of_isProfile (hg.profiles n)
  have he (n : ℕ) : convolve (F n) (G n) u - convolve f g u =
      convolve (F n - f) (G n) u + convolve f (G n - g) u := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hg.profile.2.2.1
    have hC' (t : ℝ) : |g t| ≤ C := hC _ ⟨t, rfl⟩
    have hh₁ := integrable_convolve_integrand ((hFi n).sub hfi) (hg.profiles n).1 (hG n) u
    have hh₂ := integrable_convolve_integrand hfi ((hg.profiles n).1.sub hg.profile.1)
      (fun t => (abs_sub _ _).trans (add_le_add (hG n t) (hC' t))) u
    change Integrable (fun t => f t * (G n - g) (u - t)) at hh₂
    simp only [convolve_apply]
    rw [← integral_sub (integrable_convolve_integrand (hFi n) (hg.profiles n).1 (hG n) u)
      (integrable_convolve_integrand hfi hg.profile.1 hC' u), ← integral_add hh₁ hh₂]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hlim := (hf.l1.mul_const M).add (hg.l1.mul_const B)
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (by simpa using hlim)
  rw [Real.dist_eq, he, convolve_comm f (G n - g)]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_convolve_le_of_right_bound ((hFi n).sub hfi) (hG n) u)
    (abs_convolve_le_of_right_bound ((hGi n).sub hgi) hb u))

private theorem uniformProfileBounds_of_profileConverges {k : ℕ}
    {F : ℕ → Fin k → FourierProfile} {f : Fin k → FourierProfile}
    (h : ∀ i, ProfileConverges (fun n => F n i) (f i)) : UniformProfileBounds F f := by
  classical
  choose M R hM hR hM' hR' using fun i => (h i).bounded
  refine ⟨fun i => (h i).profile, fun n i => (h i).profiles n,
    ∑ i, M i, ∑ i, R i, Finset.sum_nonneg (fun i _ => hM i),
    Finset.sum_nonneg (fun i _ => (hR i).1), ?_, ?_, ?_⟩
  · intro n i u
    exact (hM' i n u).trans (Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i))
  · intro n i
    exact (hR' i n).mono (Finset.single_le_sum (fun j _ => (hR j).1) (Finset.mem_univ i))
  · intro i
    exact (hR i).mono (Finset.single_le_sum (fun j _ => (hR j).1) (Finset.mem_univ i))

private theorem cumulant_sorted_tendsto {ι : Type*} [LinearOrder ι]
    {F : ℕ → ι → FourierProfile} {f : ι → FourierProfile} (B : Finset ι)
    (h : ∀ i ∈ B, ProfileConverges (fun n => F n i) (f i))
    (hz : B.card = 1 → ∀ i ∈ B, Tendsto (fun n => F n i 0) atTop (𝓝 (f i 0))) :
    Tendsto (fun n => cumulant ((B.sort (· ≤ ·)).map (F n))) atTop
      (𝓝 (cumulant ((B.sort (· ≤ ·)).map f))) := by
  let S := B.sort (· ≤ ·)
  have hS (i : Fin S.length) : S.get i ∈ B := (Finset.mem_sort (· ≤ ·)).mp (List.get_mem S i)
  have hc := cumulant_continuity (fun n i => F n (S.get i)) (fun i => f (S.get i))
    (uniformProfileBounds_of_profileConverges (fun i => h _ (hS i))) (fun i => (h _ (hS i)).l1)
    (fun hn i => hz (by simpa [S] using hn) _ (hS i))
  have heq (g : ι → FourierProfile) : List.ofFn (fun i : Fin S.length => g (S.get i)) = S.map g :=
    List.ofFn_getElem_eq_map S g
  simpa only [heq, S] using hc.2

/-- Continuity of the model expectation with one marked profile and two Wick-ordered lists.
Only the marked profile is used by a singleton block. -/
theorem wick_model_tendsto (A B : List FourierProfile) (h : FourierProfile)
    (F : ℕ → FourierProfile → FourierProfile) (H : ℕ → FourierProfile)
    (hH : ProfileConverges H h) (hHz : Tendsto (fun n => H n 0) atTop (𝓝 (h 0)))
    (hf : ∀ f ∈ A ++ B, ProfileConverges (fun n => F n f) f) :
    Tendsto (fun n => modelExpectation (stat (H n) * wick (A.map (F n)) * wick (B.map (F n))))
      atTop (𝓝 (modelExpectation (stat h * wick A * wick B))) := by
  classical
  let m := (A ++ B).length
  let S := h :: (A ++ B)
  let g : Fin (m + 1) → FourierProfile := Fin.cases h (A ++ B).get
  let G (n : ℕ) : Fin (m + 1) → FourierProfile := Fin.cases (H n) (fun i => F n ((A ++ B).get i))
  let kept (k l : ℕ) :=
    (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin k)))).filter fun π =>
      ∀ T ∈ π.parts, KeepWickPartition (leftLabels k l) (rightLabels k l) T
  let part {k : ℕ} (l : ℕ) (f : Fin k → FourierProfile) := ∑ π ∈ kept k l,
    ∏ T ∈ π.parts, cumulant ((T.sort (· ≤ ·)).map f)
  have hg (i : Fin (m + 1)) : ProfileConverges (fun n => G n i) (g i) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hH
    · exact hf _ (List.get_mem _ i)
  have htail : Tendsto (fun n => part A.length (G n)) atTop (𝓝 (part A.length g)) := by
    apply tendsto_finset_sum
    intro π hπ
    apply tendsto_finset_prod
    intro T hT
    apply cumulant_sorted_tendsto T (fun i _ => hg i)
    intro hcard i hi
    have hkeep := (Finset.mem_filter.mp hπ).2 T hT
    have hi0 : i = 0 := by
      by_contra hne
      apply hkeep.1
      have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
      refine ⟨i, ?_, Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j hj => ?_⟩⟩
      · rcases le_or_gt i.val A.length with hA | hA
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, hA⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
      · obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hcard
        have hjl : j = l := by simpa only [hl, Finset.mem_singleton] using hj
        have hil : i = l := by simpa only [hl, Finset.mem_singleton] using hi
        exact hjl.trans hil.symm
    subst i
    exact hHz
  have hpart {k k' : ℕ} (hk : k = k') (l : ℕ) (f : Fin k → FourierProfile) :
      part l f = part l (fun i : Fin k' => f (Fin.cast hk.symm i)) := by
    subst k'
    rfl
  have hbase : modelExpectation (stat h * wick A * wick B) = part A.length g := by
    rw [wick_moment_partition_eq _ _ _]
    · change part A.length S.get = part A.length g
      congr 1
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      rfl
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hH.profile
      · exact (hf f' hf').profile
  have hseq (n : ℕ) : modelExpectation (stat (H n) * wick (A.map (F n)) * wick (B.map (F n))) =
      part A.length (G n) := by
    rw [wick_moment_partition_eq _ _ _]
    · let V := H n :: ((A ++ B).map (F n))
      have hV : V.length = m + 1 := by simp [V, m]
      rw [← List.map_append, List.length_map]
      change part A.length V.get = part A.length (G n)
      rw [hpart hV]
      congr 1
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      change (H n :: ((A ++ B).map (F n)))[j.val + 1] = F n ((A ++ B)[j.val])
      simp only [List.getElem_cons_succ, List.getElem_map]
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hH.profiles n
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp (by rwa [List.map_append] : f' ∈ (A ++ B).map (F n))
        exact (hf g' hg').profiles n
  simpa only [hseq, hbase] using htail

end Chowla
