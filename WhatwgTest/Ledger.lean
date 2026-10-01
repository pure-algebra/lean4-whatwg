import WhatwgTest.Ledger.DataQueue
import WhatwgTest.Ledger.PromiseFirst
import WhatwgTest.Ledger.ConfigurationOrdering
import WhatwgTest.Ledger.ReadableDefault
import WhatwgTest.Ledger.WritableDefault
import WhatwgTest.Ledger.TransformBackpressure
import WhatwgTest.Ledger.PipingForwardShutdown
import WhatwgTest.Ledger.InfraUtf8
import WhatwgTest.Ledger.InfraScalar

/-!
# WhatwgTest.Ledger

The graph ledger (`test/contracts/graph-ledger.contract.md`, ruling R-W6):
every graph's entry, every leaf-receipt record, every unrouted module prefix,
and the kernel-checked statement that the ledger has no structural finding.

`ledger_wellFormed` is decided by `decide +kernel`, which evaluates
`Gates.Ledger.Ledger.wellFormed` in the kernel alone; no command, macro or
elaborator is declared. A structural defect fails `lake build` here with no
name, and `lake exe whatwg_ledger` prints the same findings, named.

Slice A holds `DATA-PG-QUEUE`, `PROMISE-PG-FIRST`,
`CONFIGURATION-PG-ORDERING` and the leaf `INFRA-LF-INTEGER`; slice B seeds the
other graphs, and slice D the unrouted prefixes of debt D57. The coordinator
owns this tree: a cell changes with the ruling that carries its edge token.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The one leaf-receipt record of the tree, `INFRA-LF-INTEGER`
(`docs/INFRA-INTEGER-CONSTRUCTIVE.md`), standalone. -/
def infraInteger : Leaf where
  id := "INFRA-LF-INTEGER"
  document := "docs/INFRA-INTEGER-CONSTRUCTIVE.md"
  declarations := [`Whatwg.Infra.Unsigned8, `Whatwg.Infra.Unsigned16, `Whatwg.Infra.Unsigned32,
    `Whatwg.Infra.Unsigned64, `Whatwg.Infra.Unsigned128, `Whatwg.Infra.Signed8,
    `Whatwg.Infra.Signed16, `Whatwg.Infra.Signed32, `Whatwg.Infra.Signed64]
  parent := none
  receipts := [
    .theorems [`Whatwg.Infra.Unsigned8.inRange, `Whatwg.Infra.Unsigned16.inRange,
      `Whatwg.Infra.Unsigned32.inRange, `Whatwg.Infra.Unsigned64.inRange,
      `Whatwg.Infra.Unsigned128.inRange, `Whatwg.Infra.Signed8.inRange,
      `Whatwg.Infra.Signed16.inRange, `Whatwg.Infra.Signed32.inRange,
      `Whatwg.Infra.Signed64.inRange],
    .ascriptions `WhatwgTest.Infra.IntegerConstructiveContract 9,
    .rows ⟨"INFRA-INTEGER-CE", 1, 1⟩ .closed]

/-- The ledger: the slice A graphs, the slice B graphs seeded so far, and the
one leaf record. -/
def ledger : Ledger where
  graphs := [dataQueue, promiseFirst, configurationOrdering, readableDefault, writableDefault,
    transformBackpressure, pipingForwardShutdown, infraUtf8, infraScalar]
  leaves := [infraInteger]

/-- The ledger has no structural finding (contract section 4). -/
theorem ledger_wellFormed : ledger.wellFormed = true := by decide +kernel

end WhatwgTest.Ledger
