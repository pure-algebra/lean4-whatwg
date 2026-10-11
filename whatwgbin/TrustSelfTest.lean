import WhatwgGates.TrustConfig
import WhatwgGates.TrustSelfTest.InProcess

/-- Entry point only; the audited logic is Gates.TrustSelfTest.InProcess.cli, over
this repository's configuration Gates.TrustConfig.config (addendum V2g). -/
def main (args : List String) : IO UInt32 :=
  Gates.TrustSelfTest.InProcess.cli Gates.TrustConfig.config args
