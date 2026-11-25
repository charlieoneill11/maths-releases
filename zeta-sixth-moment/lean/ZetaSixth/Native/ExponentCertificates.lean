import ZetaSixth.ExponentProofs.CertificateData
import ZetaSixth.ExponentProofs.Systems

namespace ZetaSixth.Exponents.NativeCertificates

open CertificateSystems

theorem completionLow :
    Farkas.checkEncoded slack (systems .completionLow) CertificateData.completionLow = true := by
  native_decide

theorem completionHigh :
    Farkas.checkEncoded slack (systems .completionHigh) CertificateData.completionHigh = true := by
  native_decide

theorem representedLow :
    Farkas.checkEncoded slack (systems .representedLow) CertificateData.representedLow = true := by
  native_decide

theorem representedMiddle :
    Farkas.checkEncoded slack (systems .representedMiddle) CertificateData.representedMiddle = true := by
  native_decide

theorem representedHigh :
    Farkas.checkEncoded slack (systems .representedHigh) CertificateData.representedHigh = true := by
  native_decide

end ZetaSixth.Exponents.NativeCertificates
