import SevenCycle.TypeTwo.Layouts
import SevenCycle.TypeTwo.Retention

/-! ## From the edges of a geometric matching to the 33-bit layout checker -/

namespace SevenCycle.TypeTwo

open Proof Blueprint.SearchSpec

/-- Pack the bits indexed by 0 through n−1, in increasing order of significance. -/
def pack (p : ℕ → Bool) : (n : ℕ) → BitVec n
  | 0 => 0
  | n+1 => BitVec.cons (p n) (pack p n)

theorem pack_bit (p : ℕ → Bool) (n i : ℕ) (hi : i < n) : (pack p n).getLsbD i = p i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pack, BitVec.getLsbD_cons]
    split
    · next h => rw [h]
    · next h => exact ih (by omega)

/-- The order may be chosen by the matching algorithm. Both endpoints use
the same index, even when their orders in S and T are different. -/
structure Numbering (M : Finset Edge) where
  edgeAt : ℕ → Edge
  inj : Set.InjOn edgeAt (Finset.range 33)
  image_eq : (Finset.range 33).image edgeAt = M

def leftOf (f : ℕ → Edge) (X : Points) : Mask :=
  pack (fun i => decide ((f i).1 ∈ X)) 33

def rightOf (f : ℕ → Edge) (Y : Points) : Mask :=
  pack (fun i => decide ((f i).2 ∈ Y)) 33

private theorem weight_eq {α : Type*} [DecidableEq α] (f : ℕ → α) (S X : Finset α)
    (hi : Set.InjOn f (Finset.range 33)) (him : (Finset.range 33).image f = S) (hX : X ⊆ S)
    (x : Mask) (hx : ∀ i < 33, x.getLsbD i = true ↔ f i ∈ X) : pop x = X.card := by
  rw [pop_eq]
  have hi' : indices x = (Finset.range 33).filter fun i => f i ∈ X := by
    ext i
    simp only [indices, Finset.mem_filter, Finset.mem_range]
    exact and_congr_right fun h => hx i h
  rw [hi']
  exact filtered_image_card f _ S X hi him hX

/-- Encoding the two actual middle levels of any Stage 2 witness produces
a full assignment satisfying every inequality used by the executable DFS. -/
theorem legal_of_middle {m : Frame} {k : Axis} {S T X Y : Points} {M : Finset Edge}
    (hM : Perfect S T M) (h : TwoMiddle m k S T X Y M) (n : Numbering M) :
    Legal (leftOf n.edgeAt X) (rightOf n.edgeAt Y) := by
  obtain ⟨hX, hY, hlo, hhi, hlo', hhi', hsingle, hempty, _⟩ := h
  obtain ⟨⟨hls,hli⟩, ⟨hrs,hri⟩⟩ := endpoint_images hM
  have hmem {i : ℕ} (hi : i < 33) : n.edgeAt i ∈ M := by
    exact (congrArg (fun D => n.edgeAt i ∈ D) n.image_eq).mp
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))
  have maps : Set.MapsTo n.edgeAt (Finset.range 33) M := fun _ hi => hmem (Finset.mem_range.mp hi)
  have leftEq : (Finset.range 33).image (Prod.fst ∘ n.edgeAt) = S := by
    rw [← Finset.image_image, n.image_eq, hls]
  have rightEq : (Finset.range 33).image (Prod.snd ∘ n.edgeAt) = T := by
    rw [← Finset.image_image, n.image_eq, hrs]
  have l := weight_eq _ S X (hli.comp n.inj maps) leftEq hX (leftOf n.edgeAt X)
    (fun i hi => by simp [leftOf, pack_bit _ _ _ hi])
  have r := weight_eq _ T Y (hri.comp n.inj maps) rightEq hY (rightOf n.edgeAt Y)
    (fun i hi => by simp [rightOf, pack_bit _ _ _ hi])
  have e := weight_eq n.edgeAt M (M.filter fun e => e.1 ∉ X ∧ e.2 ∉ Y)
    n.inj n.image_eq (Finset.filter_subset _ _) (~~~(leftOf n.edgeAt X ||| rightOf n.edgeAt Y))
    (fun i hi => by
      simp [leftOf, rightOf, hi, hmem hi, -BitVec.getLsbD_eq_getElem, pack_bit _ _ _ hi])
  refine ⟨?_, e.trans_le hempty, l ▸ hlo, l ▸ hhi, r ▸ hlo', r ▸ hhi'⟩
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_and, show (0 : Mask)[i] = false from BitVec.getElem_zero hi]
  simp only [← BitVec.getLsbD_eq_getElem, leftOf, rightOf, pack_bit _ _ _ hi]
  simpa using hsingle _ (hmem hi)

/-- If this layout is rejected, some band list fails to contain the true
restriction of any proposed mathematical middle-level witness. Together with
coverage of the list generator this excludes an actual code for that layout. -/
theorem rejectsLayout_excludes_middle {m : Frame} {k : Axis} {S T X Y : Points}
    {M : Finset Edge} (hM : Perfect S T M) (n : Numbering M) (bands : Array (Array Mark))
    (hcheck : rejectsLayout bands = true)
    (hbands : ∀ i : Fin bands.size, ∃ b ∈ bands[i],
      Realizes (leftOf n.edgeAt X) (rightOf n.edgeAt Y) b) :
    ¬ TwoMiddle m k S T X Y M :=
  fun h => rejectsLayout_sound bands hcheck ⟨_, _, legal_of_middle hM h n, hbands⟩

end SevenCycle.TypeTwo
