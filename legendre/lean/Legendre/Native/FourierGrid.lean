import Legendre.FourierGridData

namespace Legendre

theorem grid_mass_verified : checkGridMass 0.7658655 = true := by native_decide

theorem grid_moment_verified : checkGridMoment (-1.379585) = true := by native_decide

theorem gridMassUpper_lt : 2 * (gridMassUpper : ℝ) < 0.7658655 := by
  simpa using checkGridMass_sound 0.7658655 grid_mass_verified

theorem gridMomentUpper_lt : 2 * (gridMomentUpper : ℝ) < -1.379585 := by
  simpa using checkGridMoment_sound (-1.379585) grid_moment_verified

end Legendre
