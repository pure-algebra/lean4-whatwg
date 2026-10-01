import WhatwgTest.Ledger.DataQueue
import WhatwgTest.Ledger.PromiseFirst
import WhatwgTest.Ledger.ConfigurationOrdering
import WhatwgTest.Ledger.ReadableDefault
import WhatwgTest.Ledger.WritableDefault
import WhatwgTest.Ledger.TransformBackpressure
import WhatwgTest.Ledger.PipingForwardShutdown
import WhatwgTest.Ledger.InfraUtf8
import WhatwgTest.Ledger.InfraScalar
import WhatwgTest.Ledger.UrlPercent
import WhatwgTest.Ledger.UrlCensus
import WhatwgTest.Ledger.PromiseAgent

/-!
# WhatwgTest.Ledger

The graph ledger (`test/contracts/graph-ledger.contract.md`, ruling R-W6):
every graph's entry, every leaf-receipt record, every unrouted module prefix,
and the kernel-checked statement that the ledger has no structural finding.

`ledger_wellFormed` is decided by `decide +kernel`, which evaluates
`Gates.Ledger.Ledger.wellFormed` in the kernel alone; no command, macro or
elaborator is declared. A structural defect fails `lake build` here with no
name, and `lake exe whatwg_ledger` prints the same findings, named.

Slice A seeded `DATA-PG-QUEUE`, `PROMISE-PG-FIRST`,
`CONFIGURATION-PG-ORDERING` and the leaf `INFRA-LF-INTEGER`; slice B seeded the
graphs of the other nine graph documents, `PROMISE-PG-AGENT` among them, so
every graph document but the pointer `docs/SHA256-DAG.md` has an entry. Slice D
(addendum D of the contract, ruling R-W22) added the unrouted prefixes: the
module `Whatwg.Html` and twelve Infra modules, recorded by debt D57, and
`Whatwg.Streams.Kernel`, recorded by debt D68; it also added six
`Whatwg.Streams.Semantics` modules to the fence of `CONFIGURATION-PG-ORDERING`.
Since slice D, `lake exe whatwg_ledger` requires every module under `Whatwg`
that declares a constant whose name is not internal to have exactly one owner
among the graph fences, the leaf records and the unrouted prefixes, so a
landing that adds such a module adds its claim here (ruling R-W22(5)). The
coordinator owns this tree: a cell changes with the ruling that carries its
edge token.
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

/-- The ledger: the twelve graphs of slices A and B, the one leaf record, and
the fourteen unrouted prefixes of slice D (ruling R-W22): the thirteen of debt
D57, in the order of the contract's section 12, then `Whatwg.Streams.Kernel`,
of debt D68. -/
def ledger : Ledger where
  graphs := [dataQueue, promiseFirst, configurationOrdering, readableDefault, writableDefault,
    transformBackpressure, pipingForwardShutdown, infraUtf8, infraScalar, urlPercent, urlCensus,
    promiseAgent]
  leaves := [infraInteger]
  unrouted := [⟨`Whatwg.Html, "D57"⟩, ⟨`Whatwg.Infra.Namespaces, "D57"⟩,
    ⟨`Whatwg.Infra.Bytes.Byte, "D57"⟩, ⟨`Whatwg.Infra.Bytes.Sequence, "D57"⟩,
    ⟨`Whatwg.Infra.Primitive.Singleton, "D57"⟩, ⟨`Whatwg.Infra.Text.Case, "D57"⟩,
    ⟨`Whatwg.Infra.Text.Codec, "D57"⟩, ⟨`Whatwg.Infra.Text.CodePoint, "D57"⟩,
    ⟨`Whatwg.Infra.Text.Order, "D57"⟩, ⟨`Whatwg.Infra.Text.Scan, "D57"⟩,
    ⟨`Whatwg.Infra.Text.String, "D57"⟩, ⟨`Whatwg.Infra.Text.Substring, "D57"⟩,
    ⟨`Whatwg.Infra.Text.Whitespace, "D57"⟩, ⟨`Whatwg.Streams.Kernel, "D68"⟩]

/-- The ledger has no structural finding (contract section 4). -/
theorem ledger_wellFormed : ledger.wellFormed = true := by decide +kernel

end WhatwgTest.Ledger
