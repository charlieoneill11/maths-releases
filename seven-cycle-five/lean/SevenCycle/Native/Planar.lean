import SevenCycle.Atlas.PlanarKernel

/-! The former native enumeration now follows from the kernel-checked planar classification. -/

namespace SevenCycle.Native

open Atlas.Planar

theorem planar_classification : classificationCheck orbitIndices = true :=
  Kernel.planar_classification

end SevenCycle.Native
