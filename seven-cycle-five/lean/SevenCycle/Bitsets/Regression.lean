import SevenCycle.Bitsets.Counts

/-! Kernel regression checks against direct coordinate enumeration of the first
released atlas representative. They exercise all three axis conventions, the
cyclic endpoints, high-bit padding, and a signed coordinate permutation. -/
namespace SevenCycle.Bitsets

private def sample : Cube := #v[131112, 4556965019776, 70368744308740, 2751467521, 90159953494528, 41945152, 10170752041216]

private def sampleLevels : Vector (Vector Plane 7) 3 := #v[
  #v[131112, 4556965019776, 70368744308740, 2751467521, 90159953494528, 41945152, 10170752041216],
  #v[2199025418280, 9346989686912, 281475245281288, 687261876480, 4398067492864, 175939040313856, 8801461993600],
  #v[70369820025088, 290271103288320, 292594667520, 140737521975301, 360778303488, 140737509327361, 17635135719424]]

private def sampleCuts : Vector (Vector Plane 7) 3 := #v[
  #v[4556965150888, 74925709328516, 70371495776261, 90162704962049, 90159995439680, 10170793986368, 10170752172328],
  #v[11546015105192, 290822234968200, 282162507157768, 5085329369344, 180337107806720, 184740502307456, 11000487411880],
  #v[360640923313408, 290563697955840, 141030116642821, 141098300278789, 141098287630849, 158372645046785, 88004955744512]]

example : ∀ k : Fin 3, ∀ s : Fin 7, lev sample k s = (sampleLevels.get k).get s ∧
    cut sample k s = (sampleCuts.get k).get s := by decide +kernel

example : planeCard 0xfffe000000000000 = 0 ∧ cubeCard sample = 33 := by decide

example : neighbourhood 1 = 294669116252611 ∧ neighbourhood 0xfffe000000000000 = 0 := by decide

private def move : Isometry 3 := (Equiv.swap 0 2, ![true, false, false], ![1, 2, 3])

example : cubeAct move sample = #v[282024740913664, 17592489084928, 70369817952257, 2203452571652, 70437467852928, 281485714259972, 68722098320] := by decide +kernel

end SevenCycle.Bitsets
