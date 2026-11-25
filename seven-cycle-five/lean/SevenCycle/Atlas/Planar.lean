import SevenCycle.Atlas.Enumeration
import SevenCycle.Blueprint.Definitions
import SevenCycle.Proof.Bitsets
import SevenCycle.Proof.Symmetry

/-! # Classification of ten-word codes in the square -/

namespace SevenCycle.Atlas.Planar

open Proof Bitsets

private def indexOf (w : Tuple 2) : Fin 49 := ⟨index w, index_lt w⟩

private theorem indexOf_point (i : Fin 49) : indexOf (pointAt i) = i :=
  Fin.ext (index_pointAt i)

/-- The three representatives in Lemma 6, encoded by the indices 7*x+y. -/
private def representative : Fin 3 → Array (Fin 49) :=
  ![#[0, 2, 11, 14, 16, 25, 29, 34, 38, 47],
    #[0, 2, 11, 14, 23, 25, 34, 36, 38, 47],
    #[0, 2, 11, 15, 20, 24, 28, 33, 37, 46]]

private theorem rep_eq : ∀ i : Fin 3, (support (representative i)).image
    (fun p : Fin 49 => pointAt p) = Blueprint.twoRepresentatives i := by decide +kernel

def motion (i : Fin 392) : Blueprint.Isometry 2 :=
  let n := i.val
  (if n % 2 = 0 then Equiv.refl _ else Equiv.swap 0 1,
   ![n / 2 % 2 == 1, n / 4 % 2 == 1],
   ![((n / 8 / 7 : Nat) : ZMod 7), ((n / 8 % 7 : Nat) : ZMod 7)])

def orbitIndices : Array (Fin 3 × Fin 392) :=
  (Array.finRange 3).flatMap fun r => (Array.finRange 392).map fun g => (r, g)

private def moved (t : Fin 3 × Fin 392) : Array (Fin 49) :=
  (representative t.1).map fun (i : Fin 49) => indexOf (Blueprint.act (motion t.2) (pointAt i))

private def key (a : Array (Fin 49)) : UInt64 :=
  buildPlane fun w => a.contains (indexOf w)

private def orbitKeys (motions : Array (Fin 3 × Fin 392)) : Array UInt64 := motions.map (fun t => key (moved t))

/-- Planar masks used as transitions in the cube enumeration. Stabilizers may produce duplicates. -/
def maxMasks : Array UInt64 := orbitKeys orbitIndices

/-- The three literal representative masks used for the first normalized band. -/
def repMasks (r : Fin 3) : UInt64 := key (representative r)

private theorem planeSet_key (a : Array (Fin 49)) :
    planeSet (key a) = (support a).image (fun p : Fin 49 => pointAt p) := by
  ext x
  simp only [mem_planeSet, key, planeMem_buildPlane, Array.contains_iff_mem, Finset.mem_image, mem_support]
  constructor
  · intro h
    exact ⟨indexOf x, h, pointAt_index x⟩
  · rintro ⟨i, hi, rfl⟩
    simpa only [indexOf_point] using hi

theorem repMasks_correct (r : Fin 3) : planeSet (repMasks r) = Blueprint.twoRepresentatives r :=
  (planeSet_key _).trans (rep_eq r)

theorem repMasks_canonical (r : Fin 3) : Canonical (repMasks r) := by
  unfold repMasks key
  apply canonical_buildPlane

theorem maxMasks_canonical {m : UInt64} (hm : m ∈ maxMasks) : Canonical m := by
  obtain ⟨_, _, rfl⟩ := Array.mem_map.mp hm
  unfold key
  apply canonical_buildPlane

private def near (i j : Nat) : Bool :=
  i == j || (i+1) % 7 == j || (j+1) % 7 == i

private def compatible (i j : Fin 49) : Bool :=
  !(near (i.val/7) (j.val/7) && near (i.val%7) (j.val%7))

private theorem compatible_of_nonconfusable (x y : Tuple 2) (hne : x ≠ y)
    (h : ¬ conflict cycleStep x y) : compatible (indexOf x) (indexOf y) := by
  have hd : ∀ a b : Fin 49, compatible a b = false →
      ∀ k, cycleStep (pointAt a k) (pointAt b k) := by
    unfold cycleStep
    set_option maxHeartbeats 2000000 in decide +kernel
  by_contra hn
  apply h
  exact ⟨hne, by simpa [indexOf] using hd (indexOf x) (indexOf y) (by simpa using hn)⟩

/-- Exhaust the independent ten-element subsets of the 49 labelled vertices.
Every accepted leaf must match a mask constructed from a specific representative and motion. -/
def classificationCheck (motions : Array (Fin 3 × Fin 392)) : Bool :=
  let keys := orbitKeys motions
  allExtensions compatible (fun a => keys.contains (key a)) 49 10 (Array.finRange 49) #[]

private theorem checked_mask (motions : Array (Fin 3 × Fin 392)) (ok : classificationCheck motions = true)
    (C : Finset (Tuple 2)) (hc : packing cycleStep C) (hs : C.card = 10) :
    ∃ m ∈ orbitKeys motions, planeSet m = C := by
  let D := C.image indexOf
  have inj : Function.Injective indexOf := fun _ _ h => by
    simpa [indexOf] using congrArg (fun i : Fin 49 => pointAt i) h
  have sizeD : D.card = 10 := (Finset.card_image_of_injective _ inj).trans hs
  have pairs : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → compatible a b := by
    intro a ha b hb hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact compatible_of_nonconfusable x y (fun e => hne (congrArg _ e)) (hc x hx y hy)
  obtain ⟨a, ha, haD⟩ := allExtensions_sound _ _ _ _ _ _ D sizeD
    (fun i _ => Array.mem_ofFn.mpr ⟨i, rfl⟩) pairs ok
  refine ⟨key a, by simpa using ha, ?_⟩
  rw [planeSet_key, haD]
  ext x
  simp [D, support, indexOf]

theorem maxMasks_complete (ok : classificationCheck orbitIndices = true)
    (C : Finset (Tuple 2)) (hc : packing cycleStep C) (hs : C.card = 10) :
    ∃ m ∈ maxMasks, planeSet m = C := checked_mask orbitIndices ok C hc hs

theorem classificationCheck_sound (motions : Array (Fin 3 × Fin 392)) (ok : classificationCheck motions = true)
    (C : Finset (Tuple 2)) (hc : packing cycleStep C) (hs : C.card = 10) :
    ∃ r : Fin 3, ∃ g : Blueprint.Isometry 2, C = Blueprint.actOnCode g (Blueprint.twoRepresentatives r) := by
  obtain ⟨m, hm, rfl⟩ := checked_mask motions ok C hc hs
  obtain ⟨t, _, rfl⟩ := Array.mem_map.mp hm
  refine ⟨t.1, motion t.2, ?_⟩
  rw [planeSet_key, ← rep_eq]
  ext x
  simp [moved, Blueprint.actOnCode, Finset.mem_image, indexOf, Array.mem_map]

/-- Every displayed representative, and therefore every image of one, has ten codewords. -/
theorem image_valid (r : Fin 3) (g : Blueprint.Isometry 2) :
    let C := Blueprint.actOnCode g (Blueprint.twoRepresentatives r)
    packing cycleStep C ∧ C.card = 10 := by
  have rows : ∀ r : Fin 3, packing cycleStep (Blueprint.twoRepresentatives r) ∧
      (Blueprint.twoRepresentatives r).card = 10 := by
    unfold packing conflict cycleStep
    decide +kernel
  refine ⟨?_, (Finset.card_image_of_injective _
    (Function.LeftInverse.injective (Symmetry.undo_act g))).trans (rows r).2⟩
  intro x hx y hy hedge
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  exact (rows r).1 _ ha _ hb ((Symmetry.act_confusable g a b).mp hedge)

/-- Lemma 6, with the certificate for the complete fixed-size traversal as its only input. -/
theorem atlas_two (ok : classificationCheck orbitIndices = true) (C : Finset (Tuple 2)) :
    (packing cycleStep C ∧ C.card = 10) ↔
      ∃ r : Fin 3, ∃ g : Blueprint.Isometry 2, C = Blueprint.actOnCode g (Blueprint.twoRepresentatives r) := by
  constructor
  · rintro ⟨hc, hs⟩
    exact classificationCheck_sound orbitIndices ok C hc hs
  · rintro ⟨r, g, rfl⟩
    exact image_valid r g


/-- Surjectivity of the explicit mixed-radix indexing of signed affine square motions. -/
private def packMotion (swap neg0 neg1 : Bool) (t0 t1 : Fin 7) : Fin 392 :=
  ⟨swap.toNat + 2*neg0.toNat + 4*neg1.toNat + 8*t1.val + 56*t0.val, by
    have := t0.isLt
    have := t1.isLt
    cases swap <;> cases neg0 <;> cases neg1 <;> simp [Bool.toNat] <;> omega⟩

private theorem motion_surjective (g : Blueprint.Isometry 2) : ∃ j, motion j = g := by
  have pack : ∀ (sw a b : Bool) (x y : Fin 7), motion (packMotion sw a b x y) =
      (if sw then Equiv.swap 0 1 else Equiv.refl _, ![a,b], ![x,y]) := by decide +kernel
  have perms : ∀ g : Equiv.Perm (Fin 2), g = Equiv.refl _ ∨ g = Equiv.swap 0 1 := by decide
  have eta {α : Type} (f : Fin 2 → α) : ![f 0,f 1] = f := by funext j; fin_cases j <;> rfl
  rcases g with ⟨g, a, x⟩
  rcases perms g with rfl | rfl
  · exact ⟨_, by simpa only [Bool.false_eq_true, if_false, eta] using pack false (a 0) (a 1) (x 0) (x 1)⟩
  · exact ⟨_, by simpa only [if_true, eta] using pack true (a 0) (a 1) (x 0) (x 1)⟩

set_option maxRecDepth 10000 in
private theorem motion_mem (r : Fin 3) (j : Fin 392) : (r,j) ∈ orbitIndices :=
  Array.mem_flatMap.mpr ⟨r, Array.mem_ofFn.mpr ⟨r, rfl⟩,
    Array.mem_map.mpr ⟨j, Array.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩⟩

theorem maxMasks_of_orbit {C : Finset (Tuple 2)} (r : Fin 3) (g : Blueprint.Isometry 2)
    (h : C = Blueprint.actOnCode g (Blueprint.twoRepresentatives r)) :
    ∃ m ∈ maxMasks, planeSet m = C := by
  obtain ⟨j, rfl⟩ := motion_surjective g
  refine ⟨key (moved (r,j)), Array.mem_map.mpr ⟨(r,j), motion_mem r j, rfl⟩, ?_⟩
  rw [h, planeSet_key, ← rep_eq]
  ext v
  simp [moved, Blueprint.actOnCode, Finset.mem_image, indexOf, Array.mem_map]

/-- An independently established orbit classification entails the same Boolean
checker result: each completed traversal leaf is itself an independent set.
This converse permits every downstream certificate to retain its original interface. -/
theorem classificationCheck_of_orbits
    (orbits : ∀ C : Finset (Tuple 2), packing cycleStep C → C.card = 10 →
      ∃ r : Fin 3, ∃ g : Blueprint.Isometry 2,
        C = Blueprint.actOnCode g (Blueprint.twoRepresentatives r)) :
    classificationCheck orbitIndices = true := by
  let valid (A : Finset (Fin 49)) := ∀ x ∈ A, ∀ y ∈ A, x ≠ y → compatible x y = true
  let leaf := fun a => (orbitKeys orbitIndices).contains (key a)
  have cg : ∀ x y : Fin 49, compatible x y = true ↔ compatible y x = true := by decide +kernel
  have self : ∀ x : Fin 49, compatible x x = false := by decide
  have noge : ∀ x y : Fin 49, compatible x y = true →
      ¬ conflict cycleStep (pointAt x) (pointAt y) := by
    unfold conflict cycleStep
    decide +kernel
  have finish (a : Array (Fin 49)) (hsize : (support a).card = 10) (hp : valid (support a)) :
      leaf a = true := by
    let C := (support a).image (fun i : Fin 49 => pointAt i)
    have hinj : Function.Injective (fun i : Fin 49 => pointAt i) := fun _ _ e =>
      Fin.ext (by simpa using congrArg index e)
    have hC : packing cycleStep C := by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact noge _ _ (hp _ hi _ hj (fun h => hxy.1 (congrArg (fun z : Fin 49 => pointAt z) h))) hxy
    obtain ⟨r, g, hr⟩ := orbits C hC ((Finset.card_image_of_injective _ hinj).trans hsize)
    obtain ⟨m, hm, he⟩ := maxMasks_of_orbit r g hr
    have he' : key a = m := plane_eq_of_set_eq (canonical_buildPlane _) (maxMasks_canonical hm)
      ((planeSet_key a).trans he.symm)
    exact Array.contains_iff_mem.mpr (he' ▸ hm)
  have go (fuel need : Nat) (available selected : Array (Fin 49)) (enough : available.size ≤ fuel)
      (hs : (support selected).card + need = 10) (hp : valid (support selected))
      (sep : ∀ u ∈ support selected, ∀ v ∈ available, compatible u v = true) :
      allExtensions compatible leaf fuel need available selected = true := by
    induction fuel generalizing available selected need with
    | zero =>
      cases need with
      | zero => simpa only [allExtensions] using finish selected (by omega) hp
      | succ n => simp [allExtensions, show available.size < n+1 by omega]
    | succ f ih =>
      cases need with
      | zero => simpa only [allExtensions] using finish selected (by omega) hp
      | succ n =>
        by_cases hfit : n+1 ≤ available.size
        · obtain ⟨av, x, rfl⟩ := Array.exists_push_of_size_pos (by omega : 0 < available.size)
          have hx : x ∉ support selected := fun h =>
            Bool.noConfusion ((sep _ h _ (Array.mem_push_self ..)).symm.trans (self x))
          have avlen : av.size ≤ f := by simp only [Array.size_push] at enough; omega
          have hxprev : (av.push x).back = x := by simp [Array.back_eq_getElem]
          rw [allExtensions, if_neg (Nat.not_lt.mpr hfit)]
          simp only [Array.size_push, Nat.zero_lt_succ, dite_true, hxprev, Array.pop_push,
            Bool.and_eq_true]
          constructor
          · apply ih n _ (selected.push x) ((Array.size_filter_le ..).trans avlen)
            · rw [support_push, Finset.card_insert_of_notMem hx]
              omega
            · intro u hu v hv hn
              rw [support_push, Finset.mem_insert] at hu hv
              rcases hu with rfl | hu <;> rcases hv with rfl | hv
              · contradiction
              · exact (cg ..).mpr (sep _ hv _ (Array.mem_push_self ..))
              · exact sep _ hu _ (Array.mem_push_self ..)
              · exact hp u hu v hv hn
            · intro u hu v hv
              obtain ⟨hav, hvx⟩ := Array.mem_filter.mp hv
              rw [support_push, Finset.mem_insert] at hu
              rcases hu with rfl | hu
              · exact hvx
              · exact sep u hu v (Array.mem_push_of_mem _ hav)
          · exact ih (n+1) av selected avlen hs hp (fun u hu v hv => sep u hu v (Array.mem_push_of_mem _ hv))
        · simp [allExtensions, Nat.lt_of_not_ge hfit]
  exact go 49 10 (Array.finRange 49) #[] (by decide) (by decide) (by simp [valid, support])
    (by simp [support])

end SevenCycle.Atlas.Planar
