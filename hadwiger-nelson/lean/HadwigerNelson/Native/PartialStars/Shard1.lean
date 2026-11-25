import HadwigerNelson.Stars.Partial.CertificateRuntime

namespace HadwigerNelson.Stars.PartialCheck.Native

/-- Check all 3,171 threshold queries on signed source indices 35,000 through 69,999. -/
theorem shard1 : checkShard 1 = true := by native_decide

end HadwigerNelson.Stars.PartialCheck.Native
