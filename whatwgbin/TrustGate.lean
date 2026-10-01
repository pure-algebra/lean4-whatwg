import WhatwgGates.TrustConfig
import WhatwgGates.Trust.Main

/-- Entry point only; the audited logic is Gates.Trust.cli, over this repository's
configuration Gates.TrustConfig.config (addendum V2e.5). -/
def main (args : List String) : IO UInt32 := Gates.Trust.cli Gates.TrustConfig.config args
