import SevenCycleRuntime.TypeTwoGraph
import SevenCycle.TypeTwo.Encoding
import SevenCycle.Proof.Bitsets

/-! Checking the concrete matching used to prune a pair of supports. -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec

def Graph.word (x : Graph.Site) : Tuple 4 := Fin.cons 0 (Graph.coord x)

private theorem encoded_site : ∀ q : Graph.Site,
    49*(Graph.coord q 0).val + 7*(Graph.coord q 1).val + (Graph.coord q 2).val = q.val := by
  intro q
  have := q.isLt
  simp [Graph.coord, Fin.ofNat]
  omega

private theorem word_inj : Function.Injective Graph.word := by
  intro x y he
  apply Fin.ext
  rw [← encoded_site x, ← encoded_site y]
  exact congrArg (fun w : Tuple 4 => 49*(w 1).val + 7*(w 2).val + (w 3).val) he

private theorem present_eq (r : Bitsets.Cube) (x : Graph.Site) :
    Graph.present r x = Bitsets.cubeMem r (Graph.coord x) := by
  have h : ∀ y : Graph.Site, y.val % 49 = 7*(Graph.coord y 1).val + (Graph.coord y 2).val := by
    intro y
    simp [Graph.coord, Fin.ofNat]
    omega
  simp only [Graph.present, Bitsets.cubeMem, h x]
  rfl

private theorem near_step (a b : Height) : Graph.close1 a b ↔ cycleStep a b := by
  unfold cycleStep
  exact (by decide : ∀ x y : Fin 7, Graph.close1 x y ↔ x-y ∈ ({-1,0,1} : Finset (Fin 7))) a b

private theorem edge_of_near {x y : Graph.Site} (h : Graph.near x y) :
    Graph.word x = Graph.word y ∨ conflict cycleStep (Graph.word x) (Graph.word y) := by
  by_cases he : Graph.word x = Graph.word y
  · exact Or.inl he
  · refine Or.inr ⟨he, ?_⟩
    obtain ⟨⟨h0,h1⟩,h2⟩ := Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp
    intro i
    fin_cases i
    · simp [Graph.word, cycleStep]
    · exact (near_step _ _).mp h0
    · exact (near_step _ _).mp h1
    · exact (near_step _ _).mp h2

/-- Supports in the anchor face, with the omitted first coordinate restored as zero. -/
def anchorFace (r : Bitsets.Cube) : Points := (Bitsets.cubeSet r).image (Fin.cons (0 : Height))

private theorem endpoint_in_face {r : Bitsets.Cube} {x : Graph.Site} (h : Graph.present r x) :
    Graph.word x ∈ anchorFace r := Finset.mem_image.mpr
  ⟨_, (Bitsets.mem_cubeSet ..).mpr ((present_eq r x) ▸ h), rfl⟩

private theorem matching_of_graph (f : ℕ → Edge) (S T : Points) (hS : S.card = 33) (hT : T.card = 33)
    (hs : ∀ i < 33, (f i).1 ∈ S ∧ (f i).2 ∈ T ∧ ((f i).1 = (f i).2 ∨ conflict cycleStep (f i).1 (f i).2))
    (hl : Set.InjOn (Prod.fst ∘ f) (Finset.range 33)) (hr : Set.InjOn (Prod.snd ∘ f) (Finset.range 33)) :
    let M := (Finset.range 33).image f
    Perfect S T M ∧ ∃ n : Numbering M, n.edgeAt = f := by
  let I := Finset.range 33
  have surj {A : Points} {g : ℕ → Tuple 4} (hA : A.card = 33)
      (hm : ∀ i < 33, g i ∈ A) (hg : Set.InjOn g I) : I.image g = A := by
    apply Finset.eq_of_subset_of_card_le
    · rintro y hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
      exact hm _ (Finset.mem_range.mp hi)
    · rw [Finset.card_image_of_injOn hg, hA, Finset.card_range]
  have sL := surj hS (g := Prod.fst ∘ f) (fun i hi => (hs i hi).1) hl
  have sR := surj hT (g := Prod.snd ∘ f) (fun i hi => (hs i hi).2.1) hr
  refine ⟨⟨?_, ?_, ?_⟩, ⟨⟨f, ?_, rfl⟩, rfl⟩⟩
  · intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    exact hs i (Finset.mem_range.mp hi)
  · intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (sL ▸ hx : x ∈ I.image (Prod.fst ∘ f))
    refine ⟨(f i).2, Finset.mem_image.mpr ⟨i,hi,Prod.ext hix rfl⟩, ?_⟩
    intro y hy
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hy
    have ji : j = i := hl hj hi ((congrArg Prod.fst he).trans hix.symm)
    exact ji ▸ (congrArg Prod.snd he).symm
  · intro y hy
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp (sR ▸ hy : y ∈ I.image (Prod.snd ∘ f))
    refine ⟨(f i).1, Finset.mem_image.mpr ⟨i,hi,Prod.ext rfl hiy⟩, ?_⟩
    intro x hx
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hx
    have ji : j = i := hr hj hi ((congrArg Prod.snd he).trans hiy.symm)
    exact ji ▸ (congrArg Prod.fst he).symm
  · intro i hi j hj he
    exact hl hi hj (congrArg Prod.fst he)

def paired (S T : Graph.Sites) (i : Nat) : Edge :=
  (Graph.word S[Fin.ofNat 33 i],Graph.word T[Fin.ofNat 33 i])

theorem valid_matching {s t : Bitsets.Cube} {xs ys : Graph.Sites}
    (h : Graph.valid s t xs ys = true) (hs : (anchorFace s).card = 33) (ht : (anchorFace t).card = 33) :
    let f := paired xs ys
    let M := (Finset.range 33).image f
    Perfect (anchorFace s) (anchorFace t) M ∧ ∃ n : Numbering M, n.edgeAt = f := by
  have all (i : Fin 33) := Array.all_eq_true_iff_forall_mem.mp h i (Array.mem_ofFn.mpr ⟨i,rfl⟩)
  have single (i : Fin 33) :
      (Graph.present s xs[i] ∧ Graph.present t ys[i] ∧ Graph.near xs[i] ys[i]) ∧
      ∀ j : Fin 33, i = j ∨ xs[i] ≠ xs[j] ∧ ys[i] ≠ ys[j] := by
    have hi := all i
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Bool.or_eq_true,
      beq_iff_eq, bne_iff_ne] at hi
    obtain ⟨⟨⟨hx,hy⟩,hz⟩,hij⟩ := hi
    exact ⟨⟨hx,hy,hz⟩,fun j => hij j (Array.mem_ofFn.mpr ⟨j,rfl⟩)⟩
  apply matching_of_graph _ _ _ hs ht
  · intro i _
    obtain ⟨⟨hx,hy,hz⟩,_⟩ := single (Fin.ofNat 33 i)
    exact ⟨endpoint_in_face hx, endpoint_in_face hy, edge_of_near hz⟩
  all_goals
    intro i hi j hj he
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rcases (single (Fin.ofNat 33 i)).2 (Fin.ofNat 33 j) with same | ⟨hne,hne'⟩
    · simpa [Fin.ofNat, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] using congrArg Fin.val same
    · first | exact False.elim (hne (word_inj he)) | exact False.elim (hne' (word_inj he))

end SevenCycle.TypeTwo
