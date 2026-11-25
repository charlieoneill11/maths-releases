import SevenCycleRuntime.TypeTwoMiddle
import SevenCycle.TypeTwo.CertifiedMatching
import SevenCycle.TypeTwo.Sparse

/-! Soundness of the sparse index of inner planes used in the matching filter. -/

namespace SevenCycle.TypeTwo.Mid

open Proof Blueprint Blueprint.SearchSpec
open Bitsets (Cube)

theorem allowed_mem {gs : Array Planar.Grid} {g : Planar.Grid} (hg : g ∈ gs) (a : Fin 3) (t : Fin 7) :
    g[a][t] ∈ allowed gs := by
  let u := g[a][t]
  let accum (m : Allowed) (row : Vector UInt64 7) := row.toArray.foldl (fun m v => m.insert v ()) m
  apply Planar.fold_keeps gs (fun m q => q.toArray.foldl accum m) {} (fun m => u ∈ m)
    (fun s => s = g) _ (Or.inr ⟨_,hg,rfl⟩)
  intro m q h
  apply Planar.fold_keeps q.toArray accum m (fun m => u ∈ m) (fun row => row = g[a])
  · intro m row h
    apply Planar.fold_keeps row.toArray (fun (m : Allowed) v => m.insert v ()) m (fun m => u ∈ m)
      (fun v => v = u)
    · intro m v h
      rcases h with h | rfl
      · exact Std.HashMap.mem_insert.mpr (Or.inr h)
      · exact Std.HashMap.mem_insert_self
    · rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨u,Array.getElem_mem (xs := g[a].toArray) (i := t.val) (by simp),rfl⟩
  · rcases h with h | rfl
    · exact Or.inl h
    · exact Or.inr ⟨q[a],Array.getElem_mem (xs := q.toArray) (i := a.val) (by simp),rfl⟩

theorem within_index (images : Cube → Array Cube) (ss : Array Cube) (wants : Allowed)
    {r w : Cube} (hr : r ∈ ss) (hw : w ∈ images r) (hk : (Packed.key w).1 ∈ wants) :
    (w[1],w[2]) ∈ (index images ss wants).getD (Packed.key w) #[] := by
  let k := Packed.key w
  let v := (w[1],w[2])
  apply collect_covers images (fun m s => (images s).foldl (extend wants) m)
    (fun m => v ∈ m.getD k #[]) w _ ss {} r hr hw
  intro m r h
  refine Planar.fold_keeps (images r) (extend wants) m (fun m => v ∈ m.getD k #[])
    (fun u => u = w) ?_ (h.imp_right fun h => ⟨w,h,rfl⟩)
  intro tbl u h'
  by_cases he : Packed.key u = k
  · have hh : wants.contains (Packed.key u).1 := Std.HashMap.contains_iff_mem.mpr (he ▸ hk)
    rw [extend, if_pos hh, he, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_alter_self]
    simp only [Option.getD_some]
    split
    · next hb =>
      rcases h' with h' | rfl
      · simpa only [Std.HashMap.getD_eq_getD_getElem?] using h'
      · exact Array.contains_iff_mem.mp hb
    · rcases h' with h' | rfl
      · exact Array.mem_push.mpr (Or.inl (by simpa only [Std.HashMap.getD_eq_getD_getElem?] using h'))
      · exact Array.mem_push.mpr (Or.inr rfl)
  · rcases h' with h' | rfl
    · by_cases hx : wants.contains (Packed.key u).1
      · simpa only [extend, hx, if_true, Std.HashMap.getD_alter, beq_iff_eq, he, if_false] using h'
      · simpa only [extend, hx, if_false] using h'
    · exact False.elim (he rfl)

private theorem bits_eq (p : ℕ → Bool) (n : ℕ) : bits p n = pack p n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bits,pack,ih]

private theorem view_eq (xs : Graph.Sites) (a : Fin 3) (t : Fin 7) :
    view xs a t = seen (fun i => Graph.word xs[Fin.ofNat 33 i]) a.succ t := by
  simp only [view, bits_eq, seen]
  congr 1
  funext i
  let v := Graph.coord xs[Fin.ofNat 33 i] a
  change (v == t || v == t+1) = decide (v = t ∨ v = t+1)
  simp [beq_eq_decide]

private theorem flatten_eq (x : Graph.Site) (a : Fin 3) :
    flatten a x = 7*(Graph.coord x (a.succAbove 0)).val + (Graph.coord x (a.succAbove 1)).val := by
  have := x.isLt
  fin_cases a
  · change x.val % 49 = 7*(x.val/7%7) + x.val%7
    omega
  · change x.val / 49 * 7 + x.val%7 = 7*(x.val/49%7) + x.val%7
    omega
  · change x.val / 7 = 7*(x.val/49%7) + x.val/7%7
    omega

private theorem read_eq (xs : Graph.Sites) (a : Fin 3) (r : Cube) (h : Fin 7) :
    read xs a r[h] = selected (fun i => Graph.word xs[Fin.ofNat 33 i]) a.succ (planeReader r a.succ 0 h) := by
  simp only [read, bits_eq, selected]
  congr 1
  funext i
  let x := xs[Fin.ofNat 33 i]
  change r[h].toNat.testBit (flatten a x) = _
  rw [flatten_eq]
  fin_cases a <;> rfl

theorem row_marks (xs ys : Graph.Sites) (r : Cube) (a : Fin 3) (t : Fin 7) (vals : Array MiddlePair)
    (hr : (r[1],r[2]) ∈ vals) :
    markFromPlanes (paired xs ys) a.succ t (planeReader r a.succ 0 1) (planeReader r a.succ 0 2) ∈
      row xs ys a t vals := by
  apply Array.mem_map.mpr
  refine ⟨(r[1],r[2]),hr,?_⟩
  change (⟨_,_,view xs a t &&& read xs a r[1], view ys a t &&& read ys a r[2]⟩ : Mark) = _
  change (⟨view xs a t, view ys a t, view xs a t &&& read xs a (r.get (1 : Fin 7)),
    view ys a t &&& read ys a (r.get (2 : Fin 7))⟩ : Mark) = _
  rw [view_eq, view_eq]
  have h₁ : read xs a (r.get (1 : Fin 7)) = selected _ _ _ := read_eq xs a r 1
  have h₂ : read ys a (r.get (2 : Fin 7)) = selected _ _ _ := read_eq ys a r 2
  rw [h₁,h₂]
  rfl

end SevenCycle.TypeTwo.Mid
