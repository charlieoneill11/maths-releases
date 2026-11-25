import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1519_interior1_checked :
    checkLowerSlice false 150000 190000 190000 390070 118240780905 = true := by
  native_decide

end LeastPrime.Native
