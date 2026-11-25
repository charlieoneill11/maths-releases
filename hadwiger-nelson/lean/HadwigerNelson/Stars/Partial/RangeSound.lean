import HadwigerNelson.Stars.Partial.CertificateRuntime
import HadwigerNelson.Stars.Partial.Cache
import HadwigerNelson.Stars.Partial.BoxFamilies
import HadwigerNelson.Stars.CreditSound

/-! A checked shard certifies all its area-weighted query sums against the
actual rows of the partial wave. Cache resets preserve every coefficient. -/
namespace HadwigerNelson.Stars.PartialCheck
open scoped BigOperators

private theorem range_succ (arcs : Array BoxCheck.Arc) (base n : Nat) :
    rangeState arcs base (n+1) =
    let prev := rangeState arcs base n
    let next := row arcs (source (base+n)) prev.1
    (if (n+1)%2000==0 then {} else next.1,prev.2.push next.2) := rfl

private theorem range_spec (arcs : Array BoxCheck.Arc) (base n : Nat) :
    let st := rangeState arcs base n
    ValidCache st.1 ∧ st.2.size=n ∧
      ∀ i<n, st.2[i]?=some (row arcs (source (base+i)) {}).2 := by
  induction n with
  | zero =>
    exact ⟨empty_cache_valid,rfl,fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
    dsimp only at ih ⊢
    rw [range_succ]
    obtain ⟨valid,sz,all⟩ := ih
    have fresh := row_cache arcs (source (base+n)) _ valid
    refine ⟨?_,by simp [sz],?_⟩
    · split <;> first | exact empty_cache_valid | exact fresh.1
    · intro i hi
      by_cases last : i=n
      · subst i
        simp only [Array.getElem?_push,sz,ite_true,fresh.2]
      · have lb : i<n := by omega
        rw [Array.getElem?_push_lt (by omega),←Array.getElem?_eq_getElem (by omega)]
        exact all i lb

theorem range_sum (base n : Nat) (f : Row → Int) :
    (rangeRows base n).foldl (fun a r => a+f r) 0 =
      ∑ i∈Finset.range n, f (sourceRow (base+i)) := by
  have h := range_spec arcTable base n
  let rows := rangeRows base n
  have sz : rows.size=n := h.2.1
  have each (j : Fin rows.size) : rows[j.val]=sourceRow (base+j.val) := by
    have r := h.2.2 j.val (sz ▸ j.isLt)
    exact Option.some.inj ((Array.getElem?_eq_getElem j.isLt).symm.trans r)
  rw [BoxCheck.array_sum_by]
  change (∑ i : Fin rows.size,f rows[i.val])=_
  simp_rw [each]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (sourceRow (base+i))) _).trans (by rw [sz])

theorem signed_shard_sound {p : Nat} (pass : checkShard p=true) (j : Fin Data.count) :
    (Data.query j.val).lower p ≤ ∑ i∈Finset.range (length p), rowLine (sourceRow (start p+i)) (Data.query j.val) := by
  unfold checkShard at pass
  rw [Bool.and_eq_true] at pass
  have h := pass.1
  have hi := (BoxCheck.array_all_ofFn _).1 h j
  change decide ((Data.query j.val).lower p ≤ directScore (rangeRows (start p) (length p)) (Data.query j.val)) = true at hi
  simpa only [directScore,range_sum] using (of_decide_eq_true hi)

private theorem checkNative_sound {base count : Nat} (d : Nat) (hd : 1≤d) (bound : d≤89)
    (pass : checkNative (rangeRows base count)=true) :
    Data.native d ≤ ∑ i∈Finset.range count, rowNative (sourceRow (base+i)) d := by
  let j : Fin 89 := ⟨d-1,by omega⟩
  have ij : j.val+1=d := by dsimp [j];omega
  have hi := (BoxCheck.array_all_ofFn _).1 pass j
  change decide (Data.native (j.val+1) ≤ directNative (rangeRows base count) (j.val+1))=true at hi
  rw [ij] at hi
  simpa only [directNative,range_sum] using (of_decide_eq_true hi)

private theorem extract_native (p : Nat) (pass : checkShard p=true) (eq : p=3) :
    checkNative (rangeRows 132621 4122)=true := by
  unfold checkShard at pass
  rw [Bool.and_eq_true] at pass
  simpa only [eq,bne_self_eq_false,Bool.false_or] using pass.2

/-- The last shard also checks the exact native sums needed for all 88 finite
degrees and the monotone tail starting at 89. -/
theorem native_shard_sound (pass : checkShard 3=true) (d : Nat) (hd : 1≤d) (bound : d≤89) :
    Data.native d ≤ ∑ i∈Finset.range 4122, rowNative (sourceRow (132621+i)) d :=
  checkNative_sound d hd bound (extract_native 3 pass rfl)

theorem all_shards_sound (pass : ∀p : Fin 4,checkShard p.val=true) (j : Fin Data.count) :
    total (Data.query j.val) ≤ ∑ i : Fin 132621, rowLine (sourceRow i.val) (Data.query j.val) := by
  let q := Data.query j.val
  let f (i : Nat) := rowLine (sourceRow i) q
  have h0 := signed_shard_sound (pass ⟨0,by decide⟩) j
  have h1 := signed_shard_sound (pass ⟨1,by decide⟩) j
  have h2 := signed_shard_sound (pass ⟨2,by decide⟩) j
  have h3 := signed_shard_sound (pass ⟨3,by decide⟩) j
  change q.first ≤ ∑ i∈Finset.range 35000, f (0+i) at h0
  change q.second ≤ ∑ i∈Finset.range 35000, f (35000+i) at h1
  change q.third ≤ ∑ i∈Finset.range 35000, f (70000+i) at h2
  change q.fourth ≤ ∑ i∈Finset.range 27621, f (105000+i) at h3
  simp only [Nat.zero_add] at h0
  change q.first+q.second+q.third+q.fourth ≤ ∑i : Fin 132621, f i.val
  rw [Fin.sum_univ_eq_sum_range]
  change _ ≤ ∑ i∈Finset.range ((35000+35000+35000)+27621), f i
  rw [Finset.sum_range_add,Finset.sum_range_add,Finset.sum_range_add]
  exact add_le_add (add_le_add (add_le_add h0 h1) h2) h3

end HadwigerNelson.Stars.PartialCheck
