import SevenCycleRuntime.PlaneSearch
import SevenCycle.Atlas.CubePlanes

namespace SevenCycle.Atlas.MaskSearch

open SevenCycleRuntime.PlaneSearch
open Proof Bitsets

private theorem cell_spec : ∀ i : Fin 49, planeSet (cell i) = {pointAt i} := by
  intro i
  ext x
  have hi := index_lt x
  have bit : ∀ i j : Fin 49, (cell i).toNat.testBit j = decide (i = j) := by decide +kernel
  simp only [mem_planeSet, planeMem, Finset.mem_singleton]
  rw [show (cell i).toNat.testBit (index x) = decide (i = ⟨index x, hi⟩) from bit i ⟨index x, hi⟩,
    decide_eq_true_eq]
  constructor
  · rintro rfl; exact (pointAt_index x).symm
  · rintro rfl; exact Fin.ext (index_pointAt i).symm

private theorem cell_canonical (i : Fin 49) : Canonical (cell i) := by
  have h : ∀ i : Fin 49, (cell i).toNat < 2^49 := by decide +kernel
  intro j hj
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (h i) (Nat.pow_le_pow_right (by decide) hj))

private def blocked : Vector UInt64 49 := Vector.ofFn fun i => neighbourhood (cell i)

private theorem bit_not (p : Plane) (x : Tuple 2) : planeMem (~~~p) x = !planeMem p x := by
  have hi : index x < 64 := Nat.lt_trans (index_lt x) (by decide)
  change (~~~p).toBitVec.getLsbD (index x) = !p.toBitVec.getLsbD (index x)
  simp [UInt64.toBitVec_not, hi]

private theorem size_le (D : Finset (Tuple 2)) (j : Nat) (bound : ∀ x ∈ D, index x < j) : D.card ≤ j := by
  have inj : Function.Injective index := fun _ _ h => by simpa using congrArg pointAt h
  rw [← Finset.card_image_of_injective _ inj, ← Finset.card_range j]
  exact Finset.card_le_card (by rintro x hx; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_range.mpr (bound y hy))

private theorem all_sound (visit : Plane → Bool) (i need : Nat) (available chosen : Plane)
    (D : Finset (Tuple 2)) (hi : i ≤ 49) (hcan : Canonical chosen)
    (hD : D ⊆ planeSet available) (bits : ∀ x ∈ D, index x < i)
    (hs : D.card = need) (hc : packing cycleStep D)
    (ok : all blocked visit i need available chosen = true) :
    ∃ v, visit v = true ∧ planeSet v = planeSet chosen ∪ D ∧ Canonical v := by
  induction i generalizing need available chosen D with
  | zero =>
    have hem : D = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => Nat.not_lt_zero _ (bits x hx)
    subst D
    simp at hs
    subst need
    exact ⟨chosen, by simpa [all] using ok, by simp, hcan⟩
  | succ j ih =>
    by_cases hn : need = 0
    · have hem := Finset.card_eq_zero.mp (hs.trans hn)
      exact ⟨chosen, by simpa [hn, all] using ok, by simp [hem], hcan⟩
    have le := size_le D (j+1) bits
    have hz : available ≠ 0 := by
      rintro rfl
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
      simpa [planeMem] using hD hx
    have hi' : j < 49 := by omega
    let u : Tuple 2 := pointAt j
    have hb := cell_spec ⟨j, hi'⟩
    change planeSet (cell j) = {u} at hb
    have rem (x : Tuple 2) (hx : x ∈ D) (hne : x ≠ u) : index x < j := by
      have hlt := bits x hx
      have hne' : index x ≠ j := fun e => hne (by simpa [u] using congrArg pointAt e)
      omega
    have bcan := cell_canonical ⟨j,hi'⟩
    rw [all] at ok
    simp only [beq_eq_false_iff_ne.mpr hn, Bool.false_eq_true, if_false,
      decide_eq_false (by omega : ¬need > j+1), beq_eq_false_iff_ne.mpr hz,
      Bool.false_or] at ok
    have xor_mem (x : Tuple 2) (hx : x ∈ D) (hne : x ≠ u) :
        x ∈ planeSet (available ^^^ cell j) := by
      have hno : x ∉ planeSet (cell j) := by simpa [hb] using hne
      have hfalse : planeMem (cell j) x = false := Bool.eq_false_iff.mpr (fun h => hno ((mem_planeSet ..).mpr h))
      have hav := (mem_planeSet ..).mp (hD hx)
      apply (mem_planeSet ..).mpr
      change (available ^^^ cell j).toNat.testBit (index x) = true
      rw [UInt64.toNat_xor, Nat.testBit_xor, show (cell j).toNat.testBit (index x) = false from hfalse]
      simpa using hav
    split at ok
    · rename_i absent
      have hu : u ∉ D := by
        intro hu
        have hboth : u ∈ planeSet (available &&& cell j) := (planeSet_and ..) ▸ Finset.mem_inter.mpr ⟨hD hu, by simp [hb]⟩
        rw [beq_iff_eq.mp absent] at hboth
        simp [planeMem] at hboth
      exact ih _ _ _ _ (by omega) hcan hD (fun x hx => rem x hx (fun e => hu (e ▸ hx))) hs hc ok
    · have ⟨hy,hn'⟩ := Bool.and_eq_true_iff.mp ok
      by_cases hu : u ∈ D
      · let R := D.erase u
        have hfree : R ⊆ planeSet ((available ^^^ cell j) &&& ~~~blocked[j]!) := by
          intro x hx
          obtain ⟨hne, hxD⟩ := Finset.mem_erase.mp hx
          rw [planeSet_and]
          refine Finset.mem_inter.mpr ⟨xor_mem x hxD hne, ?_⟩
          rw [mem_planeSet, bit_not, Bool.not_eq_true', Bool.eq_false_iff]
          have hb' : blocked[j]! = neighbourhood (cell j) := by simp [blocked, getElem!_pos, hi']
          rw [hb']
          intro h
          obtain ⟨y, hy, hclose⟩ := (mem_neighbourhood ..).mp ((mem_planeSet ..).mpr h)
          have he : y = u := by simpa [hb] using hy
          exact hc x hxD u hu ⟨hne, he ▸ hclose⟩
        obtain ⟨v, hv, he, hcv⟩ := ih _ _ _ R (by omega) (canonical_or hcan bcan) hfree
          (fun x hx => rem x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.mp hx).1)
          (by simp [R, Finset.card_erase_of_mem hu, hs])
          (fun x hx y hy => hc x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) hy
        refine ⟨v, hv, he.trans ?_, hcv⟩
        rw [planeSet_or, hb]
        ext x
        simp only [R, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
        by_cases h : x = u <;> simp_all
      · exact ih _ _ _ D (by omega) hcan (fun x hx => xor_mem x hx (fun e => hu (e ▸ hx)))
          (fun x hx => rem x hx (fun e => hu (e ▸ hx))) hs hc hn'

def visitNew (p : Plane) (need : Nat) (visit : Plane → Bool) : Bool :=
  all blocked visit 49 need (~~~neighbourhood p) 0

theorem visitNew_sound {p q : Plane} (hq : Canonical q) (hc : packing cycleStep (planeSet q))
    (hfree : compatible q p) (need : Nat) (hsize : planeCard q = need)
    (visit : Plane → Bool) (h : visitNew p need visit = true) : visit q = true := by
  have hav : planeSet q ⊆ planeSet (~~~neighbourhood p) := by
    intro x hx
    rw [mem_planeSet, bit_not, Bool.not_eq_true', Bool.eq_false_iff]
    intro bad
    obtain ⟨y, hy, hnear⟩ := (mem_neighbourhood ..).mp ((mem_planeSet ..).mpr bad)
    exact (compatible_iff ..).mp hfree x hx y hy hnear
  obtain ⟨v, hv, he, hcan⟩ := all_sound visit 49 need _ 0 (planeSet q) (by decide)
    (by intro i _; simp) hav (fun x _ => index_lt x) ((planeCard_eq q).symm.trans hsize) hc h
  have hzero : planeSet 0 = ∅ := by ext; simp [planeMem]
  rwa [plane_eq_of_set_eq hcan hq (by simpa [hzero] using he)] at hv

end SevenCycle.Atlas.MaskSearch
