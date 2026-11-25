import Legendre.Arithmetic.BridgeNumeric
import Legendre.ShoulderGridData

namespace Legendre.Arithmetic

theorem firstRow_charge_verified : rowChargeChecker firstRow shoulderHeight = true := by
  native_decide

theorem secondRow_charge_verified : rowChargeChecker secondRow shoulderHeight = true := by
  native_decide

theorem firstRow_verified (he : ShoulderSteps shoulderHeight) :
    BridgeRowChecks firstRow shoulderHeight (fun j ↦ (rowOffset firstRow j : ℝ)) :=
  rowChargeChecker_sound _ _ he firstRow_base_verified firstRow_charge_verified

theorem secondRow_verified (he : ShoulderSteps shoulderHeight) :
    BridgeRowChecks secondRow shoulderHeight (fun j ↦ (rowOffset secondRow j : ℝ)) :=
  rowChargeChecker_sound _ _ he secondRow_base_verified secondRow_charge_verified

end Legendre.Arithmetic
