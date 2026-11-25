import HadwigerNelson.Stars.Partial.DegreeFacts.Block10
import HadwigerNelson.Stars.CreditSound

/-! Combine the 88 kernel-reduced Fejér tables and the native-only tail. -/
namespace HadwigerNelson.Stars.PartialCheck

private theorem degree_checked (d : Nat) (hd : 0 < d) (h : d ≤ 88) : degreePass d = true := by
  match d with
  | 0 => omega
  | 1 => exact DegreeFacts.checked01
  | 2 => exact DegreeFacts.checked02
  | 3 => exact DegreeFacts.checked03
  | 4 => exact DegreeFacts.checked04
  | 5 => exact DegreeFacts.checked05
  | 6 => exact DegreeFacts.checked06
  | 7 => exact DegreeFacts.checked07
  | 8 => exact DegreeFacts.checked08
  | 9 => exact DegreeFacts.checked09
  | 10 => exact DegreeFacts.checked10
  | 11 => exact DegreeFacts.checked11
  | 12 => exact DegreeFacts.checked12
  | 13 => exact DegreeFacts.checked13
  | 14 => exact DegreeFacts.checked14
  | 15 => exact DegreeFacts.checked15
  | 16 => exact DegreeFacts.checked16
  | 17 => exact DegreeFacts.checked17
  | 18 => exact DegreeFacts.checked18
  | 19 => exact DegreeFacts.checked19
  | 20 => exact DegreeFacts.checked20
  | 21 => exact DegreeFacts.checked21
  | 22 => exact DegreeFacts.checked22
  | 23 => exact DegreeFacts.checked23
  | 24 => exact DegreeFacts.checked24
  | 25 => exact DegreeFacts.checked25
  | 26 => exact DegreeFacts.checked26
  | 27 => exact DegreeFacts.checked27
  | 28 => exact DegreeFacts.checked28
  | 29 => exact DegreeFacts.checked29
  | 30 => exact DegreeFacts.checked30
  | 31 => exact DegreeFacts.checked31
  | 32 => exact DegreeFacts.checked32
  | 33 => exact DegreeFacts.checked33
  | 34 => exact DegreeFacts.checked34
  | 35 => exact DegreeFacts.checked35
  | 36 => exact DegreeFacts.checked36
  | 37 => exact DegreeFacts.checked37
  | 38 => exact DegreeFacts.checked38
  | 39 => exact DegreeFacts.checked39
  | 40 => exact DegreeFacts.checked40
  | 41 => exact DegreeFacts.checked41
  | 42 => exact DegreeFacts.checked42
  | 43 => exact DegreeFacts.checked43
  | 44 => exact DegreeFacts.checked44
  | 45 => exact DegreeFacts.checked45
  | 46 => exact DegreeFacts.checked46
  | 47 => exact DegreeFacts.checked47
  | 48 => exact DegreeFacts.checked48
  | 49 => exact DegreeFacts.checked49
  | 50 => exact DegreeFacts.checked50
  | 51 => exact DegreeFacts.checked51
  | 52 => exact DegreeFacts.checked52
  | 53 => exact DegreeFacts.checked53
  | 54 => exact DegreeFacts.checked54
  | 55 => exact DegreeFacts.checked55
  | 56 => exact DegreeFacts.checked56
  | 57 => exact DegreeFacts.checked57
  | 58 => exact DegreeFacts.checked58
  | 59 => exact DegreeFacts.checked59
  | 60 => exact DegreeFacts.checked60
  | 61 => exact DegreeFacts.checked61
  | 62 => exact DegreeFacts.checked62
  | 63 => exact DegreeFacts.checked63
  | 64 => exact DegreeFacts.checked64
  | 65 => exact DegreeFacts.checked65
  | 66 => exact DegreeFacts.checked66
  | 67 => exact DegreeFacts.checked67
  | 68 => exact DegreeFacts.checked68
  | 69 => exact DegreeFacts.checked69
  | 70 => exact DegreeFacts.checked70
  | 71 => exact DegreeFacts.checked71
  | 72 => exact DegreeFacts.checked72
  | 73 => exact DegreeFacts.checked73
  | 74 => exact DegreeFacts.checked74
  | 75 => exact DegreeFacts.checked75
  | 76 => exact DegreeFacts.checked76
  | 77 => exact DegreeFacts.checked77
  | 78 => exact DegreeFacts.checked78
  | 79 => exact DegreeFacts.checked79
  | 80 => exact DegreeFacts.checked80
  | 81 => exact DegreeFacts.checked81
  | 82 => exact DegreeFacts.checked82
  | 83 => exact DegreeFacts.checked83
  | 84 => exact DegreeFacts.checked84
  | 85 => exact DegreeFacts.checked85
  | 86 => exact DegreeFacts.checked86
  | 87 => exact DegreeFacts.checked87
  | 88 => exact DegreeFacts.checked88
  | n + 89 => omega

/-- The complete choice of frequencies and thresholds is checked by the kernel. -/
theorem data_checked : dataPass = true := by
  unfold dataPass
  rw [Bool.and_eq_true]
  refine ⟨(BoxCheck.array_all_ofFn _).2 (fun i => degree_checked (i.val+1) (by omega) (by omega)), ?_⟩
  decide +kernel

end HadwigerNelson.Stars.PartialCheck
