import SevenCycle.TypeTwo.Global
import SevenCycle.Native.TypeTwo.Chunk00
import SevenCycle.Native.TypeTwo.Chunk01
import SevenCycle.Native.TypeTwo.Chunk02
import SevenCycle.Native.TypeTwo.Chunk03
import SevenCycle.Native.TypeTwo.Chunk04
import SevenCycle.Native.TypeTwo.Chunk05
import SevenCycle.Native.TypeTwo.Chunk06
import SevenCycle.Native.TypeTwo.Chunk07
import SevenCycle.Native.TypeTwo.Chunk08
import SevenCycle.Native.TypeTwo.Chunk09
import SevenCycle.Native.TypeTwo.Chunk10
import SevenCycle.Native.TypeTwo.Chunk11
import SevenCycle.Native.TypeTwo.Chunk12
import SevenCycle.Native.TypeTwo.Chunk13
import SevenCycle.Native.TypeTwo.Chunk14
import SevenCycle.Native.TypeTwo.Chunk15
import SevenCycle.Native.TypeTwo.Chunk16
import SevenCycle.Native.TypeTwo.Chunk17
import SevenCycle.Native.TypeTwo.Chunk18
import SevenCycle.Native.TypeTwo.Chunk19
import SevenCycle.Native.TypeTwo.Chunk20
import SevenCycle.Native.TypeTwo.Chunk21
import SevenCycle.Native.TypeTwo.Chunk22
import SevenCycle.Native.TypeTwo.Chunk23
import SevenCycle.Native.TypeTwo.Chunk24
import SevenCycle.Native.TypeTwo.Chunk25
import SevenCycle.Native.TypeTwo.Chunk26
import SevenCycle.Native.TypeTwo.Chunk27
import SevenCycle.Native.TypeTwo.Chunk28
import SevenCycle.Native.TypeTwo.Chunk29
import SevenCycle.Native.TypeTwo.Chunk30
import SevenCycle.Native.TypeTwo.Chunk31
import SevenCycle.Native.TypeTwo.Chunk32
import SevenCycle.Native.TypeTwo.Chunk33
import SevenCycle.Native.TypeTwo.Chunk34
import SevenCycle.Native.TypeTwo.Chunk35
import SevenCycle.Native.TypeTwo.Chunk36
import SevenCycle.Native.TypeTwo.Chunk37
import SevenCycle.Native.TypeTwo.Chunk38
import SevenCycle.Native.TypeTwo.Chunk39
import SevenCycle.Native.TypeTwo.Chunk40
import SevenCycle.Native.TypeTwo.Chunk41
import SevenCycle.Native.TypeTwo.Chunk42
import SevenCycle.Native.TypeTwo.Chunk43
import SevenCycle.Native.TypeTwo.Chunk44
import SevenCycle.Native.TypeTwo.Chunk45
import SevenCycle.Native.TypeTwo.Chunk46
import SevenCycle.Native.TypeTwo.Chunk47
import SevenCycle.Native.TypeTwo.Chunk48
import SevenCycle.Native.TypeTwo.Chunk49
import SevenCycle.Native.TypeTwo.Chunk50
import SevenCycle.Native.TypeTwo.Chunk51
import SevenCycle.Native.TypeTwo.Chunk52
import SevenCycle.Native.TypeTwo.Chunk53
import SevenCycle.Native.TypeTwo.Chunk54
import SevenCycle.Native.TypeTwo.Chunk55
import SevenCycle.Native.TypeTwo.Chunk56
import SevenCycle.Native.TypeTwo.Chunk57
import SevenCycle.Native.TypeTwo.Chunk58
import SevenCycle.Native.TypeTwo.Chunk59
import SevenCycle.Native.TypeTwo.Chunk60
import SevenCycle.Native.TypeTwo.Chunk61
import SevenCycle.Native.TypeTwo.Chunk62
import SevenCycle.Native.TypeTwo.Chunk63

namespace SevenCycle.TypeTwo.Search

/-- Every opposite class has been checked against every source representative. -/
theorem all_chunks (i : Fin 64) : chunk i.val = true := by
  fin_cases i
  · exact Native.typeTwo_chunk_00
  · exact Native.typeTwo_chunk_01
  · exact Native.typeTwo_chunk_02
  · exact Native.typeTwo_chunk_03
  · exact Native.typeTwo_chunk_04
  · exact Native.typeTwo_chunk_05
  · exact Native.typeTwo_chunk_06
  · exact Native.typeTwo_chunk_07
  · exact Native.typeTwo_chunk_08
  · exact Native.typeTwo_chunk_09
  · exact Native.typeTwo_chunk_10
  · exact Native.typeTwo_chunk_11
  · exact Native.typeTwo_chunk_12
  · exact Native.typeTwo_chunk_13
  · exact Native.typeTwo_chunk_14
  · exact Native.typeTwo_chunk_15
  · exact Native.typeTwo_chunk_16
  · exact Native.typeTwo_chunk_17
  · exact Native.typeTwo_chunk_18
  · exact Native.typeTwo_chunk_19
  · exact Native.typeTwo_chunk_20
  · exact Native.typeTwo_chunk_21
  · exact Native.typeTwo_chunk_22
  · exact Native.typeTwo_chunk_23
  · exact Native.typeTwo_chunk_24
  · exact Native.typeTwo_chunk_25
  · exact Native.typeTwo_chunk_26
  · exact Native.typeTwo_chunk_27
  · exact Native.typeTwo_chunk_28
  · exact Native.typeTwo_chunk_29
  · exact Native.typeTwo_chunk_30
  · exact Native.typeTwo_chunk_31
  · exact Native.typeTwo_chunk_32
  · exact Native.typeTwo_chunk_33
  · exact Native.typeTwo_chunk_34
  · exact Native.typeTwo_chunk_35
  · exact Native.typeTwo_chunk_36
  · exact Native.typeTwo_chunk_37
  · exact Native.typeTwo_chunk_38
  · exact Native.typeTwo_chunk_39
  · exact Native.typeTwo_chunk_40
  · exact Native.typeTwo_chunk_41
  · exact Native.typeTwo_chunk_42
  · exact Native.typeTwo_chunk_43
  · exact Native.typeTwo_chunk_44
  · exact Native.typeTwo_chunk_45
  · exact Native.typeTwo_chunk_46
  · exact Native.typeTwo_chunk_47
  · exact Native.typeTwo_chunk_48
  · exact Native.typeTwo_chunk_49
  · exact Native.typeTwo_chunk_50
  · exact Native.typeTwo_chunk_51
  · exact Native.typeTwo_chunk_52
  · exact Native.typeTwo_chunk_53
  · exact Native.typeTwo_chunk_54
  · exact Native.typeTwo_chunk_55
  · exact Native.typeTwo_chunk_56
  · exact Native.typeTwo_chunk_57
  · exact Native.typeTwo_chunk_58
  · exact Native.typeTwo_chunk_59
  · exact Native.typeTwo_chunk_60
  · exact Native.typeTwo_chunk_61
  · exact Native.typeTwo_chunk_62
  · exact Native.typeTwo_chunk_63

end SevenCycle.TypeTwo.Search
