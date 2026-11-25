import SevenCycle.TypeThree.Join
import Std.Data.HashMap.Lemmas

/-! A two-key index for the eight-band test. The first index stores the
possible transverse supports for each ordered pair of plane masks. A second
index groups the potential opposite anchors by any two chosen cut slots. -/

namespace SevenCycle.TypeThree

private theorem bucket_add (m : Index) (x y a b : UInt64) (r : CutRow) :
    bucket (addRow m x y r) a b = if x = a ∧ y = b then (bucket m a b).push r else bucket m a b := by
  by_cases hx : x = a <;> by_cases hy : y = b <;>
    simp [bucket, addRow, Std.HashMap.getElem?_alter, Std.HashMap.getD_eq_getD_getElem?, *]

theorem makeIndex_covers (f g : CutRow → UInt64) (rows : Array CutRow) {r : CutRow} (h : r ∈ rows) :
    r ∈ bucket (makeIndex f g rows) (f r) (g r) := by
  have hfold := Array.foldl_induction (as := rows)
    (f := fun m t => addRow m (f t) (g t) t)
    (init := ({} : Index))
    (motive := fun n m => ∀ i : Fin rows.size, i.val < n → rows[i] ∈ bucket m (f rows[i]) (g rows[i]))
    (by intro i hi; omega) (by
      intro i m hm j hj
      rw [bucket_add]
      by_cases hji : j = i
      · subst j; simp
      · have hj' : j.val < i.val := by
          have : j.val ≠ i.val := fun e => hji (Fin.ext e)
          omega
        split
        · exact Array.mem_push.mpr (.inl (hm j hj'))
        · exact hm j hj')
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp h
  exact hfold ⟨i, hi⟩ hi

private theorem rightKey_mem {d : Index} {x y : UInt64} {r : CutRow}
    (h : r ∈ bucket d x y) : y ∈ d.getD x {} := by
  by_contra hn
  simp [bucket, Std.HashMap.getD_eq_fallback hn] at h

private theorem rejectsPair_sound {d : Index} {s t a a' b b' c c' : CutRow}
    (h : rejectsPair (sourceDomains d s) t) (j : Joined s t a a' b b' c c')
    (ha : a ∈ bucket d a.a0 a.a3) (ha' : a' ∈ bucket d a'.a0 a'.a3)
    (hb : b ∈ bucket d b.a0 b.a3) (hb' : b' ∈ bucket d b'.a0 b'.a3)
    (hc : c ∈ bucket d c.a0 c.a3) (hc' : c' ∈ bucket d c'.a0 c'.a3) : False := by
  rw [j.A0.1, j.A0.2] at ha
  rw [j.A3.1, j.A3.2] at ha'
  rw [j.B0.1, j.B0.2] at hb
  rw [j.B3.1, j.B3.2] at hb'
  rw [j.C0.1, j.C0.2] at hc
  rw [j.C3.1, j.C3.2] at hc'
  have hjoin : rejectJoin (bucket d s.a0 t.a0) (bucket d s.a3 t.a3)
      (bucket d s.b0 t.b0) (bucket d s.b3 t.b3) (bucket d s.c0 t.c0) (bucket d s.c3 t.c3) := by
    simpa [rejectsPair, sourceDomains, bucket, Std.HashMap.contains_iff_mem.mpr (rightKey_mem hb),
      Std.HashMap.contains_iff_mem.mpr (rightKey_mem hb'),
      Std.HashMap.contains_iff_mem.mpr (rightKey_mem hc),
      Std.HashMap.contains_iff_mem.mpr (rightKey_mem hc')] using h
  exact rejectJoin_sound hjoin ha ha' hb hb' hc hc' j.cross

private theorem joined_keys {s t a a' b b' c c' : CutRow} (j : Joined s t a a' b b' c c')
    (d : Index) (ha : a ∈ bucket d a.a0 a.a3) (ha' : a' ∈ bucket d a'.a0 a'.a3)
    (hb : b ∈ bucket d b.a0 b.a3) (hb' : b' ∈ bucket d b'.a0 b'.a3)
    (hc : c ∈ bucket d c.a0 c.a3) (hc' : c' ∈ bucket d c'.a0 c'.a3) (k : Fin 6) :
    slot t k ∈ d.getD (slot s k) {} := by
  fin_cases k
  · simpa [j.A0.1, j.A0.2, slot] using rightKey_mem ha
  · simpa [j.A3.1, j.A3.2, slot] using rightKey_mem ha'
  · simpa [j.B0.1, j.B0.2, slot] using rightKey_mem hb
  · simpa [j.B3.1, j.B3.2, slot] using rightKey_mem hb'
  · simpa [j.C0.1, j.C0.2, slot] using rightKey_mem hc
  · simpa [j.C3.1, j.C3.2, slot] using rightKey_mem hc'

private theorem checkBuckets_sound (allowed groups : Buckets) (ok : CutRow → Bool)
    (h : checkBuckets allowed groups ok) {y : UInt64} (hy : y ∈ allowed)
    {r : CutRow} (hr : r ∈ groups.getD y #[]) : ok r := by
  unfold checkBuckets at h
  split at h
  · exact Array.all_eq_true'.mp
      (Std.HashMap.all_eq_true_iff_forall_mem_getElem.mp h y hy) r hr
  · have hg : y ∈ groups := by
      by_contra hn
      simp [Std.HashMap.getD_eq_fallback hn] at hr
    have ht := Std.HashMap.all_eq_true_iff_forall_mem_getElem.mp h y hg
    have hc := Std.HashMap.contains_iff_mem.mpr hy
    rw [hc, Bool.not_true, Bool.false_or, Std.HashMap.getElem_eq_getD (fallback := #[])] at ht
    exact Array.all_eq_true'.mp ht r hr

theorem rejectsSource_sound (all : Array CutRow) (d q : Index) (i j : Fin 6) (s : CutRow)
    (cov : ∀ r ∈ all, r ∈ bucket d r.a0 r.a3)
    (query : ∀ r ∈ all, r ∈ bucket q (slot r i) (slot r j)) (rs : rejectsSource d q i j s) :
    ∀ t ∈ all, ∀ a ∈ all, ∀ a' ∈ all, ∀ b ∈ all, ∀ b' ∈ all, ∀ c ∈ all, ∀ c' ∈ all,
      ¬ Joined s t a a' b b' c c' := by
  intro t ht a ha a' ha' b hb b' hb' c hc c' hc' joint
  have key := joined_keys joint d (cov _ ha) (cov _ ha') (cov _ hb) (cov _ hb')
    (cov _ hc) (cov _ hc')
  have rx := Std.HashMap.all_eq_true_iff_forall_mem_getElem.mp rs (slot t i) (key i)
  have rt := checkBuckets_sound _ _ _ rx (key j) (query t ht)
  exact rejectsPair_sound rt joint (cov _ ha) (cov _ ha') (cov _ hb) (cov _ hb') (cov _ hc) (cov _ hc')

theorem checkSources_sound (sources all : Array CutRow) (i j : Fin 6)
    (h : checkSources sources all i j = true) : NoJoined sources all := by
  intro s hs
  exact rejectsSource_sound all _ _ i j s (fun _ hr => makeIndex_covers _ _ _ hr)
    (fun _ hr => makeIndex_covers _ _ _ hr) (Array.all_eq_true'.mp h s hs)

end SevenCycle.TypeThree
