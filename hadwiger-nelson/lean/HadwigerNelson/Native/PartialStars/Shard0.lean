import HadwigerNelson.Stars.Partial.CertificateRuntime

namespace HadwigerNelson.Stars.PartialCheck.Native

/-- Check all 3,171 threshold queries on signed source indices 0 through 34,999. -/
theorem shard0 : checkShard 0 = true := by native_decide

end HadwigerNelson.Stars.PartialCheck.Native
