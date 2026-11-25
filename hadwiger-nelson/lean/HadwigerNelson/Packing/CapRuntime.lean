import Mathlib.Data.Rat.Floor

namespace HadwigerNelson.Packing

inductive AnnulusChoice where
  | disk
  | single (k : ℕ)
  | split (j outer inner : ℕ)

/-- Trial annuli indexed by the inclusive upper hundredth. Every returned trial is
rechecked over the rationals before it can improve the disk bound. -/
def annulusHints : Array (ℕ × AnnulusChoice) := #[
  (100, .disk), (115, .single 6), (130, .single 7), (146, .single 8),
  (161, .single 9), (168, .single 10), (173, .single 11), (177, .single 12),
  (180, .single 13), (182, .single 14), (184, .single 15), (186, .single 16),
  (187, .single 17), (189, .single 18), (190, .single 19), (194, .split 13 7 12),
  (199, .split 13 7 13), (203, .split 13 7 14), (205, .split 14 8 13), (208, .split 16 9 12),
  (210, .split 14 8 14), (211, .split 15 9 13), (216, .split 16 9 13), (222, .split 16 9 14),
  (226, .split 16 9 15), (230, .split 16 9 16), (234, .split 16 9 17), (236, .split 16 9 18),
  (237, .split 17 11 16), (239, .split 16 9 19), (241, .split 17 11 17), (244, .split 17 11 18),
  (246, .split 17 11 19), (247, .split 18 13 17), (248, .split 17 11 20), (251, .split 18 13 18),
  (254, .split 18 13 19), (256, .split 18 13 20), (258, .split 18 13 21), (260, .split 18 13 22),
  (262, .split 18 13 23), (263, .split 18 13 24), (265, .split 18 13 25), (266, .split 18 13 26),
  (267, .split 18 13 27), (268, .split 19 19 22), (270, .split 19 19 23), (272, .split 19 19 24),
  (273, .split 19 19 25), (274, .split 19 19 26), (275, .split 19 19 27), (276, .split 19 19 28),
  (277, .split 19 19 29), (278, .split 19 19 30), (279, .split 19 19 31), (280, .split 19 19 33),
  (281, .split 19 19 34), (282, .split 19 19 37), (283, .split 19 19 39), (284, .split 19 19 42),
  (285, .split 19 19 46), (286, .split 19 19 52), (287, .split 19 19 60), (288, .split 19 19 73),
  (289, .split 19 19 104), (400, .disk)]

def annulusTest (a b : ℚ) (k : ℕ) : Bool :=
  let ψ := (44:ℚ)/(7*(k+1:ℕ))
  let c := max ((2*a^2-1)/(2*a^2)) (max ((a^2+b^2-1)/(2*a*b)) ((2*b^2-1)/(2*b^2)))
  decide (4 ≤ k ∧ k ≤ 127 ∧ c < 1-ψ^2/2+ψ^4/24-ψ^6/720)

def checkedRing (M : ℕ) : Option ℕ :=
  let hi := (M:ℚ)/100
  let choice := ((annulusHints.find? fun e ↦ M ≤ e.1).map Prod.snd).getD .disk
  match choice with
  | .disk => none
  | .single k => if annulusTest 1 hi k then some k else none
  | .split j k h =>
    if 11 ≤ j ∧ 10*j < M ∧ annulusTest 1 ((j:ℚ)/10) k ∧ annulusTest ((j:ℚ)/10) hi h
    then some (k+h) else none

/-- Validate and cache the 401 hundredth-grid annulus choices once per certificate. -/
def ringTable : Array (Option ℕ) := Array.ofFn fun i : Fin 401 ↦ checkedRing i.val

def capUpper (ρ t : ℚ) : ℕ :=
  if t ≤ ρ then 0 else
    let A := ⌊(1+2*t/ρ)^2⌋₊-1
    let M := ⌈100*t/ρ⌉₊
    match (ringTable[M]?).join with
    | some k => min A k
    | none => A

end HadwigerNelson.Packing
