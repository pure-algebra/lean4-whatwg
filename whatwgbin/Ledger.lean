import WhatwgGates.Ledger.Check
import WhatwgTest.Ledger

/-- Entry point only; the audited logic is Gates.Ledger.cli, over the ledger
data of `WhatwgTest/Ledger.lean` (test/contracts/graph-ledger.contract.md,
section 10). -/
def main (args : List String) : IO UInt32 :=
  Gates.Ledger.cli WhatwgTest.Ledger.ledger args
