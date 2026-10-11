import Whatwg
import WhatwgTest.Audit.BankCensus

/-! An invocation of the bank census (ruling R-S10 of `COORDINATION.md`). Run it from the
repository root after `lake build`:

    lake env lean workshop/BankCensus.lean

No module imports this file, and no gate reads its output. -/

#whatwg_bank_census "Whatwg" "WhatwgTest"