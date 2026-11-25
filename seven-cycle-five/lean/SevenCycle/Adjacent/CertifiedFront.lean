import SevenCycle.Adjacent.FrontSearch
import SevenCycle.Native.Adjacent.Block000
import SevenCycle.Native.Adjacent.Block001
import SevenCycle.Native.Adjacent.Block002
import SevenCycle.Native.Adjacent.Block003
import SevenCycle.Native.Adjacent.Block004
import SevenCycle.Native.Adjacent.Block005
import SevenCycle.Native.Adjacent.Block006
import SevenCycle.Native.Adjacent.Block007
import SevenCycle.Native.Adjacent.Block008
import SevenCycle.Native.Adjacent.Block009
import SevenCycle.Native.Adjacent.Block010
import SevenCycle.Native.Adjacent.Block011
import SevenCycle.Native.Adjacent.Block012
import SevenCycle.Native.Adjacent.Block013
import SevenCycle.Native.Adjacent.Block014
import SevenCycle.Native.Adjacent.Block015
import SevenCycle.Native.Adjacent.Block016
import SevenCycle.Native.Adjacent.Block017
import SevenCycle.Native.Adjacent.Block018
import SevenCycle.Native.Adjacent.Block019
import SevenCycle.Native.Adjacent.Block020
import SevenCycle.Native.Adjacent.Block021
import SevenCycle.Native.Adjacent.Block022
import SevenCycle.Native.Adjacent.Block023
import SevenCycle.Native.Adjacent.Block024
import SevenCycle.Native.Adjacent.Block025
import SevenCycle.Native.Adjacent.Block026
import SevenCycle.Native.Adjacent.Block027
import SevenCycle.Native.Adjacent.Block028
import SevenCycle.Native.Adjacent.Block029
import SevenCycle.Native.Adjacent.Block030
import SevenCycle.Native.Adjacent.Block031
import SevenCycle.Native.Adjacent.Block032
import SevenCycle.Native.Adjacent.Block033
import SevenCycle.Native.Adjacent.Block034
import SevenCycle.Native.Adjacent.Block035
import SevenCycle.Native.Adjacent.Block036
import SevenCycle.Native.Adjacent.Block037
import SevenCycle.Native.Adjacent.Block038
import SevenCycle.Native.Adjacent.Block039
import SevenCycle.Native.Adjacent.Block040
import SevenCycle.Native.Adjacent.Block041
import SevenCycle.Native.Adjacent.Block042
import SevenCycle.Native.Adjacent.Block043
import SevenCycle.Native.Adjacent.Block044
import SevenCycle.Native.Adjacent.Block045
import SevenCycle.Native.Adjacent.Block046
import SevenCycle.Native.Adjacent.Block047
import SevenCycle.Native.Adjacent.Block048
import SevenCycle.Native.Adjacent.Block049
import SevenCycle.Native.Adjacent.Block050
import SevenCycle.Native.Adjacent.Block051
import SevenCycle.Native.Adjacent.Block052
import SevenCycle.Native.Adjacent.Block053
import SevenCycle.Native.Adjacent.Block054
import SevenCycle.Native.Adjacent.Block055
import SevenCycle.Native.Adjacent.Block056
import SevenCycle.Native.Adjacent.Block057
import SevenCycle.Native.Adjacent.Block058
import SevenCycle.Native.Adjacent.Block059
import SevenCycle.Native.Adjacent.Block060
import SevenCycle.Native.Adjacent.Block061
import SevenCycle.Native.Adjacent.Block062
import SevenCycle.Native.Adjacent.Block063
import SevenCycle.Native.Adjacent.Block064

namespace SevenCycle.Adjacent.FrontSearch

private def first (j : Fin 65) : Nat := if j.val = 0 then 0 else 1+16*(j.val-1)
private def last (j : Fin 65) : Nat := if j.val = 0 then 1 else min 1016 (1+16*j.val)

attribute [local irreducible] range PrefixHint.needed

private theorem block_passes (j : Fin 65) :
    range PrefixHint.needed (first j) (last j) = true := by
  fin_cases j
  · exact Native.adjacent_block000
  · exact Native.adjacent_block001
  · exact Native.adjacent_block002
  · exact Native.adjacent_block003
  · exact Native.adjacent_block004
  · exact Native.adjacent_block005
  · exact Native.adjacent_block006
  · exact Native.adjacent_block007
  · exact Native.adjacent_block008
  · exact Native.adjacent_block009
  · exact Native.adjacent_block010
  · exact Native.adjacent_block011
  · exact Native.adjacent_block012
  · exact Native.adjacent_block013
  · exact Native.adjacent_block014
  · exact Native.adjacent_block015
  · exact Native.adjacent_block016
  · exact Native.adjacent_block017
  · exact Native.adjacent_block018
  · exact Native.adjacent_block019
  · exact Native.adjacent_block020
  · exact Native.adjacent_block021
  · exact Native.adjacent_block022
  · exact Native.adjacent_block023
  · exact Native.adjacent_block024
  · exact Native.adjacent_block025
  · exact Native.adjacent_block026
  · exact Native.adjacent_block027
  · exact Native.adjacent_block028
  · exact Native.adjacent_block029
  · exact Native.adjacent_block030
  · exact Native.adjacent_block031
  · exact Native.adjacent_block032
  · exact Native.adjacent_block033
  · exact Native.adjacent_block034
  · exact Native.adjacent_block035
  · exact Native.adjacent_block036
  · exact Native.adjacent_block037
  · exact Native.adjacent_block038
  · exact Native.adjacent_block039
  · exact Native.adjacent_block040
  · exact Native.adjacent_block041
  · exact Native.adjacent_block042
  · exact Native.adjacent_block043
  · exact Native.adjacent_block044
  · exact Native.adjacent_block045
  · exact Native.adjacent_block046
  · exact Native.adjacent_block047
  · exact Native.adjacent_block048
  · exact Native.adjacent_block049
  · exact Native.adjacent_block050
  · exact Native.adjacent_block051
  · exact Native.adjacent_block052
  · exact Native.adjacent_block053
  · exact Native.adjacent_block054
  · exact Native.adjacent_block055
  · exact Native.adjacent_block056
  · exact Native.adjacent_block057
  · exact Native.adjacent_block058
  · exact Native.adjacent_block059
  · exact Native.adjacent_block060
  · exact Native.adjacent_block061
  · exact Native.adjacent_block062
  · exact Native.adjacent_block063
  · exact Native.adjacent_block064

/-- The checked intervals exhaust every possible target representative. -/
theorem checked : ScanFused.checkClasses atlasPlanes (gate PrefixHint.needed) SlabTables.leaf = true := by
  apply of_ranges
  intro i
  have size : atlasPlanes.size = 1016 := by decide +kernel
  have lt : i.val < 1016 := size ▸ i.isLt
  by_cases start : i.val = 0
  · refine ⟨0,1,by omega,by omega,block_passes 0⟩
  · let j : Fin 65 := ⟨(i.val-1)/16 + 1, by omega⟩
    have nz : j.val ≠ 0 := Nat.succ_ne_zero _
    have bl : first j ≤ i.val := by
      change (if j.val = 0 then 0 else 1+16*(j.val-1)) ≤ i.val
      rw [if_neg nz]
      dsimp [j]
      omega
    have en : i.val < last j := by
      change i.val < if j.val = 0 then 1 else min 1016 (1+16*j.val)
      rw [if_neg nz]
      apply lt_min lt
      dsimp [j]
      omega
    exact ⟨_,_,bl,en,block_passes j⟩

end SevenCycle.Adjacent.FrontSearch
