import HadwigerNelson.Centres.ThresholdDefs
import HadwigerNelson.Packing.Disks
import HadwigerNelson.Packing.PairCounts

/-! Disk packing at the seven physical radii in Lemma 51. Both the count
of internal ordered pairs and the number touching the complement are explicit. -/

namespace HadwigerNelson.Centres
open Finset Packing
noncomputable section
attribute [local instance] Classical.propDecidable

def closeOrdered (A B : Finset Plane) (r : ℝ) : Finset (Plane × Plane) :=
  (A ×ˢ B).filter fun s => s.1≠s.2 ∧ dist s.1 s.2<r

theorem closeOrdered_card (A B : Finset Plane) (r : ℝ) :
    (closeOrdered A B r).card=between A B r := by
  simp only [closeOrdered,between,closeNeighbours,card_filter,sum_product]

private theorem threshold_pos (i : Fin 7) : 0<threshold i := by
  unfold threshold tenths δ
  positivity

theorem threshold_disk (D : Finset Plane) (sep : separated D δ) (x : Plane) (i : Fin 7) :
    (D.filter fun y => dist x y<threshold i).card≤diskLimit i := by
  let S := D.filter fun y => dist x y < threshold i
  have hp := disks S x (ρ:=δ/2) (R:=threshold i) (by norm_num [δ]) (threshold_pos i).le
    (fun a ha b hb ne => by
      simpa only [mul_div_cancel₀ _ (two_ne_zero: (2:ℝ)≠0)] using
        sep a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 ne)
    (fun z hz => (dist_comm z x).le.trans (mem_filter.mp hz).2.le)
  have eq : 1+threshold i/(δ/2)=(10+2*(tenths i:ℝ))/10 := by unfold threshold δ; ring
  rw [eq] at hp
  apply (Nat.le_div_iff_mul_le (by decide : 0<100)).mpr
  have : (S.card:ℝ)*100≤(10+2*(tenths i:ℝ))^2 := by linarith only [hp]
  exact_mod_cast this

private theorem threshold_close (D : Finset Plane) (sep : separated D δ) (x : Plane) (i : Fin 7) :
    (closeNeighbours D x (threshold i)).card≤diskLimit i := by
  apply le_trans _ (threshold_disk D sep x i)
  apply card_le_card
  intro z hz; exact mem_filter.mpr ⟨(mem_filter.mp hz).1,(mem_filter.mp hz).2.2⟩

private theorem threshold_close_self (D : Finset Plane) (sep : separated D δ) (x : Plane) (hx : x∈D) (i : Fin 7) :
    (closeNeighbours D x (threshold i)).card≤diskLimit i-1 := by
  let N := closeNeighbours D x (threshold i)
  have nx : x∉N := fun h => (mem_filter.mp h).2.1 rfl
  have sub : insert x N ⊆ D.filter (fun z => dist x z<threshold i) := by
    intro z hz
    rcases mem_insert.mp hz with rfl|h
    · exact mem_filter.mpr ⟨hx,by simpa using threshold_pos i⟩
    · exact mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.2⟩
  have bound := (card_le_card sub).trans (threshold_disk D sep x i)
  rw [card_insert_of_notMem nx] at bound
  change N.card≤_; omega

theorem inside_pair_cap (D : Finset Plane) (sep : separated D δ) (i : Fin 7) :
    (closeOrdered D D (threshold i)).card ≤ (diskLimit i-1)*D.card := by
  rw [closeOrdered_card,mul_comm]
  exact between_bound D D (threshold i) _ (fun x hx => threshold_close_self D sep x hx i)

def outsideClose (X D : Finset Plane) (r : ℝ) : Finset (Plane × Plane) :=
  (closeOrdered X X r).filter fun s => s.1∉D ∨ s.2∉D

theorem outside_pair_cap (X D : Finset Plane) (sub : D⊆X) (sep : separated D δ) (i : Fin 7) :
    (outsideClose X D (threshold i)).card ≤ 2*(diskLimit i*(X.card-D.card)+(X.card-D.card).choose 2) := by
  let r := threshold i
  let O := X\D
  have part := between_partition X D r sub
  have count := (closeOrdered X X r).card_filter_add_card_filter_not (fun s => s.1∉D ∨ s.2∉D)
  have within : ((closeOrdered X X r).filter fun s => ¬(s.1∉D ∨ s.2∉D))=closeOrdered D D r := by
    ext z
    simp only [closeOrdered,mem_filter,mem_product,not_or,not_not]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨⟨sub h.1.1,sub h.1.2⟩,h.2⟩,h.1⟩⟩
  rw [within,closeOrdered_card,closeOrdered_card] at count
  have outer := between_self_bound O r
  have cross := between_bound O D r (diskLimit i) (fun x _ => threshold_close D sep x i)
  have oc : O.card=X.card-D.card := card_sdiff_of_subset sub
  change (outsideClose X D r).card+between D D r=between X X r at count
  change between X X r=between O O r+2*between O D r+between D D r at part
  rw [mul_comm (diskLimit i),← oc]
  change (outsideClose X D r).card ≤ 2*(O.card*diskLimit i+O.card.choose 2)
  omega

end
end HadwigerNelson.Centres
