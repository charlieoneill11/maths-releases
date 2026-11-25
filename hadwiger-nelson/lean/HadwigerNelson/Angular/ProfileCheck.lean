import HadwigerNelson.Angular.Constants
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace HadwigerNelson.CompleteWave

set_option Elab.async false
set_option maxRecDepth 16000

private theorem block00 : checkBlock 0 = true := by decide +kernel
private theorem block01 : checkBlock 1 = true := by decide +kernel
private theorem block02 : checkBlock 2 = true := by decide +kernel
private theorem block03 : checkBlock 3 = true := by decide +kernel
private theorem block04 : checkBlock 4 = true := by decide +kernel
private theorem block05 : checkBlock 5 = true := by decide +kernel
private theorem block06 : checkBlock 6 = true := by decide +kernel
private theorem block07 : checkBlock 7 = true := by decide +kernel
private theorem block08 : checkBlock 8 = true := by decide +kernel
private theorem block09 : checkBlock 9 = true := by decide +kernel
private theorem block10 : checkBlock 10 = true := by decide +kernel
private theorem block11 : checkBlock 11 = true := by decide +kernel
private theorem block12 : checkBlock 12 = true := by decide +kernel
private theorem block13 : checkBlock 13 = true := by decide +kernel
private theorem block14 : checkBlock 14 = true := by decide +kernel
private theorem block15 : checkBlock 15 = true := by decide +kernel
private theorem block16 : checkBlock 16 = true := by decide +kernel
private theorem block17 : checkBlock 17 = true := by decide +kernel
private theorem block18 : checkBlock 18 = true := by decide +kernel
private theorem block19 : checkBlock 19 = true := by decide +kernel
private theorem block20 : checkBlock 20 = true := by decide +kernel
private theorem block21 : checkBlock 21 = true := by decide +kernel
private theorem block22 : checkBlock 22 = true := by decide +kernel
private theorem block23 : checkBlock 23 = true := by decide +kernel
private theorem block24 : checkBlock 24 = true := by decide +kernel
private theorem block25 : checkBlock 25 = true := by decide +kernel
private theorem block26 : checkBlock 26 = true := by decide +kernel
private theorem block27 : checkBlock 27 = true := by decide +kernel
private theorem block28 : checkBlock 28 = true := by decide +kernel
private theorem block29 : checkBlock 29 = true := by decide +kernel
private theorem block30 : checkBlock 30 = true := by decide +kernel
private theorem block31 : checkBlock 31 = true := by decide +kernel
private theorem block32 : checkBlock 32 = true := by decide +kernel
private theorem block33 : checkBlock 33 = true := by decide +kernel
private theorem block34 : checkBlock 34 = true := by decide +kernel
private theorem block35 : checkBlock 35 = true := by decide +kernel
private theorem block36 : checkBlock 36 = true := by decide +kernel
private theorem block37 : checkBlock 37 = true := by decide +kernel
private theorem block38 : checkBlock 38 = true := by decide +kernel
private theorem block39 : checkBlock 39 = true := by decide +kernel
private theorem block40 : checkBlock 40 = true := by decide +kernel
private theorem block41 : checkBlock 41 = true := by decide +kernel
private theorem block42 : checkBlock 42 = true := by decide +kernel
private theorem block43 : checkBlock 43 = true := by decide +kernel
private theorem block44 : checkBlock 44 = true := by decide +kernel
private theorem block45 : checkBlock 45 = true := by decide +kernel
private theorem block46 : checkBlock 46 = true := by decide +kernel
private theorem block47 : checkBlock 47 = true := by decide +kernel
private theorem block48 : checkBlock 48 = true := by decide +kernel
private theorem block49 : checkBlock 49 = true := by decide +kernel
private theorem block50 : checkBlock 50 = true := by decide +kernel
private theorem block51 : checkBlock 51 = true := by decide +kernel
private theorem block52 : checkBlock 52 = true := by decide +kernel
private theorem block53 : checkBlock 53 = true := by decide +kernel
private theorem block54 : checkBlock 54 = true := by decide +kernel
private theorem block55 : checkBlock 55 = true := by decide +kernel
private theorem block56 : checkBlock 56 = true := by decide +kernel
private theorem block57 : checkBlock 57 = true := by decide +kernel
private theorem block58 : checkBlock 58 = true := by decide +kernel
private theorem block59 : checkBlock 59 = true := by decide +kernel
private theorem block60 : checkBlock 60 = true := by decide +kernel
private theorem block61 : checkBlock 61 = true := by decide +kernel
private theorem block62 : checkBlock 62 = true := by decide +kernel
private theorem block63 : checkBlock 63 = true := by decide +kernel
private theorem block64 : checkBlock 64 = true := by decide +kernel

theorem validProfile : ValidProfile := by
  apply validProfile_of_blocks
  intro k
  fin_cases k
  · exact block00
  · exact block01
  · exact block02
  · exact block03
  · exact block04
  · exact block05
  · exact block06
  · exact block07
  · exact block08
  · exact block09
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59
  · exact block60
  · exact block61
  · exact block62
  · exact block63
  · exact block64

end HadwigerNelson.CompleteWave
