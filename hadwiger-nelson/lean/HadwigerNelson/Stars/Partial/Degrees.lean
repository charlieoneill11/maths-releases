import HadwigerNelson.Stars.Partial.CertificateRuntime
import HadwigerNelson.Stars.Partial.BoxFamilies
import HadwigerNelson.Stars.CreditSound
import HadwigerNelson.Stars.Fejer

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (quant)
noncomputable section

private theorem weighted_conversion {K d : Nat} (hd : 0<d) (t : Fin K → Nat)
    (test : (d:Int)*(∑k : Fin K,2*((K:Int)-(k.val:Int))*(t k : Int)*(t k : Int)) <
      ((K:Int)+1-d)*((K:Int)+1)*10000^2) :
    (∑k : Fin K,fejerWeight K k*((t k:ℝ)/10000)^2) < ((K:ℝ)+1)/d-1 := by
  have D : (0:ℝ)<d := by exact_mod_cast hd
  have Kp : 0<(K:ℝ)+1 := by positivity
  have r : (d:ℝ)*(∑ k : Fin K, 2*((K:ℝ)-k.val)*(t k:ℝ)*(t k:ℝ)) <
      ((K:ℝ)+1-d)*((K:ℝ)+1)*10000^2 := by exact_mod_cast test
  have norm : (∑k : Fin K,fejerWeight K k*((t k:ℝ)/10000)^2) =
      (∑k : Fin K,2*((K:ℝ)-k.val)*(t k:ℝ)*(t k:ℝ))/(((K:ℝ)+1)*10000^2) := by
    rw [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    unfold fejerWeight
    field_simp
    ring
  rw [norm,lt_sub_iff_add_lt,lt_div_iff₀ D]
  set S := ∑ k : Fin K, 2*((K:ℝ)-k.val)*(t k:ℝ)*(t k:ℝ)
  field_simp
  linarith only [r]

theorem degree_facts (d : Nat) (hd : 0<d) (pass : degreePass d=true) :
    let ids := Data.degree d
    0 < ids.size ∧ ids.size≤frequencyCount ∧
    (∀ i : Fin ids.size, ids[i.val]<Data.count ∧
      (queryAt ids i.val).harmonic=i.val ∧ (queryAt ids i.val).threshold≤10000 ∧
      thresholdTarget d (Data.native d) (total (queryAt ids i.val))=true) ∧
    (∑ i : Fin ids.size,fejerWeight ids.size i*((((queryAt ids i.val).threshold:Nat):ℝ)/10000)^2)
      < ((ids.size:ℝ)+1)/d-1 := by
  let ids := Data.degree d
  simp only [degreePass,Bool.and_eq_true,decide_eq_true_eq] at pass
  obtain ⟨⟨⟨pos,cap⟩,tests⟩,fejer⟩ := pass
  refine ⟨pos,cap,?_,?_⟩
  · intro i
    have w := (BoxCheck.array_all_ofFn _).1 tests i
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at w
    simpa only [queryAt,Array.getElem?_eq_getElem i.isLt,Option.getD_some] using
      And.intro w.1.1.1 ⟨w.1.1.2,w.1.2,w.2⟩
  · apply weighted_conversion hd
    simpa only [BoxCheck.array_sum_ofFn] using fejer

theorem target_value (d : Nat) (hd : 0<d) (high value : Int)
    (pass : thresholdTarget d high value=true) :
    (901:ℝ)/10^12 ≤ 2*value/(PartialWave.xInt*quant*10000:ℝ) +
      4*high/(PartialWave.xInt*quant*d:ℝ) := by
  have step : (901:Int)*PartialWave.xInt*quant*10000*(d:Int) ≤
      (4*high*10000+2*value*(d:Int))*scale := of_decide_eq_true pass
  have casted : (901:ℝ)*PartialWave.xInt*quant*10000*(d:ℝ) ≤
      (4*high*10000+2*value*(d:ℝ))*scale := by exact_mod_cast step
  have D : (0:ℝ)<d := by exact_mod_cast hd
  norm_num [PartialWave.xInt,quant,scale] at casted ⊢
  field_simp [D.ne']
  linarith only [casted]

theorem some_frequency {d : Nat} (hd : 0<d) (φ : Fin d → ℝ) (pass : degreePass d=true) :
    let ids := Data.degree d
    ∃ i : Fin ids.size, ((queryAt ids i.val).threshold:ℝ)/10000 ≤ powerFraction φ i.val := by
  let ids := Data.degree d
  obtain ⟨_,_,_,bound⟩ := degree_facts d hd pass
  have req := fejer_bound hd (fun j => anglePhase (φ j)) (fun j => by
    rw [←Complex.sq_norm,norm_anglePhase];norm_num) ids.size
  have actual : ((ids.size:ℝ)+1)/d-1 ≤
      ∑ i : Fin ids.size, fejerWeight ids.size i*(powerFraction φ i.val)^2 := by
    simpa only [powerFraction,div_pow,Complex.sq_norm] using req
  dsimp only
  by_contra! no
  apply (not_lt_of_ge actual) (lt_of_le_of_lt _ bound)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold powerFraction;positivity) (no i).le 2)
    (fejerWeight_nonneg _)

theorem data_facts (pass : dataPass=true) :
    (∀ d, 0<d → d≤88 → degreePass d=true) ∧ thresholdTarget 89 (Data.native 89) 0=true := by
  unfold dataPass at pass
  rw [Bool.and_eq_true] at pass
  have bits := pass
  refine ⟨?_,bits.2⟩
  intro d pd bd
  let n : Fin 88 := ⟨d-1,by omega⟩
  have eq : n.val+1=d := by dsimp [n];omega
  simpa only [eq] using (BoxCheck.array_all_ofFn _).1 bits.1 n

end
end HadwigerNelson.Stars.PartialCheck
