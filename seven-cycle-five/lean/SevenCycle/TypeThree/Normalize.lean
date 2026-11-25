import SevenCycle.Proof.Crossings
import SevenCycle.TypeThree.Coverage

/-! # Normalisation of the two marked bands on every axis

First put the projection of one full band into the atlas. This can move the
three transverse pairs. Translate those three axes to put each pair back at
starts 0 and 3. Consequently the anchor is a translation of an atlas row. No
minimality assumption on the chosen row or on the class of any other band is
required for this version of the search. -/

namespace SevenCycle.TypeThree
open SevenCycle.Blueprint SevenCycle.Proof

abbrev AtlasComplete := ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 33 →
  ∃ r : Fin atlasPlanes.size, ∃ g : Isometry 3, D = actOnCode g (atlasRepresentative r)

def translation {n : ℕ} (v : Tuple n) : Isometry n := (Equiv.refl _, fun _ => false, v)

private theorem keeps_packing {n : ℕ} (g : Isometry n) {D : Finset (Tuple n)}
    (hd : packing cycleStep D) : packing cycleStep (actOnCode g D) := by
  intro x hx y hy he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  exact hd a ha b hb ((Symmetry.act_confusable g a b).mp he)

private theorem full_moved (C : Finset (Tuple 4)) (g : Isometry 4) (k : Fin 4)
    (a : ZMod 7) (h : a ∈ fullStarts C (g.1 k)) :
    Crossings.startValue (g.2.1 k) (g.2.2 k) a ∈ fullStarts (actOnCode g C) k :=
  (Crossings.full_transport C g (Function.LeftInverse.injective (f := act g) (g := act (Symmetry.undo g)) (Symmetry.undo_act g)) k a).mpr h

private theorem transport_pairs {C : Finset (Tuple 4)} (g : Isometry 4)
    (h : ∀ k, ∃ a ∈ fullStarts C k, a+3 ∈ fullStarts C k) (k : Fin 4) :
    ∃ a ∈ fullStarts (actOnCode g C) k, a+3 ∈ fullStarts (actOnCode g C) k := by
  obtain ⟨a, ha, hb⟩ := h (g.1 k)
  have h0 := full_moved C g k a ha
  have h3 := full_moved C g k (a+3) hb
  cases e : g.2.1 k with
  | false =>
    refine ⟨_, h0, ?_⟩
    simpa [Crossings.startValue, e, add_assoc, add_left_comm, add_comm] using h3
  | true =>
    refine ⟨_, h3, ?_⟩
    have swap : ∀ a v : ZMod 7,
        Crossings.startValue true v (a+3) + 3 = Crossings.startValue true v a := by decide
    rw [e, swap]
    simpa [e] using h0

theorem normalize (atlas : AtlasComplete) {C : Finset (Tuple 4)} (hC : packing cycleStep C)
    (hfull : ∀ k, ∃ a ∈ fullStarts C k, a+3 ∈ fullStarts C k) :
    ∃ D : Finset (Tuple 4), packing cycleStep D ∧
      (∀ k, 0 ∈ fullStarts D k ∧ 3 ∈ fullStarts D k) ∧
      ∃ r : Fin atlasPlanes.size, ∃ v : Tuple 3,
        projectedBand D 0 0 = actOnCode (translation v) (atlasRepresentative r) := by
  obtain ⟨i, hi, hi3⟩ := hfull 0
  obtain ⟨γ, _, _, hK, _, h0, h3, r, hr⟩ :=
    Crossings.normalise_full_pair atlas C hC 0 i 3 hi hi3
  let K := actOnCode γ C
  choose starts hstarts hnext using transport_pairs γ hfull
  let base : Tuple 4 := Fin.cons 0 (fun j => starts j.succ)
  have hb (k : Fin 4) : base k ∈ fullStarts K k ∧ base k + 3 ∈ fullStarts K k := by
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [base] using And.intro h0 h3
    · exact ⟨hstarts _, hnext _⟩
  let δ := translation (fun k => -base k)
  let v : Tuple 3 := fun j => -base j.succ
  refine ⟨actOnCode δ K, keeps_packing δ hK, ?_, r, v, ?_⟩
  · intro k
    have hs := full_moved K δ k (base k) (hb k).1
    have ht := full_moved K δ k (base k + 3) (hb k).2
    simpa [δ, translation, Crossings.startValue, add_assoc, add_left_comm, add_comm]
      using And.intro hs ht
  · have hband := Crossings.image_band K δ 0 0
    have ez : Crossings.startValue (δ.2.1 0) (δ.2.2 0) 0 = 0 := by
      simp [Crossings.startValue, δ, translation, base]
    rw [ez] at hband
    rw [← hr]
    change (band (actOnCode δ K) 0 0).image (dropCoord 0) =
      ((band K 0 0).image (dropCoord 0)).image (act (translation v))
    rw [hband, Finset.image_image, Finset.image_image]
    congr 1

end SevenCycle.TypeThree
