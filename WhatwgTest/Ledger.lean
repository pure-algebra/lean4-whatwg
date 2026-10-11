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
import WhatwgTest.Ledger.SvgSeam

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

/-- The leaf-receipt record `SVG-LF-GRAMMAR`: the value-grammar library of slice S4a of
`docs/SVG-PACKAGE-PLAN.md` and the grammars of slices S4b to S4d, each an exact
representation whose laws the library proves once, with the reader's rule as a relation, its
bridge to the expression's language and the located refusal of a text. It contributes to the
representation edge of `SVG-PG-SEAM`. -/
def svgGrammar : Leaf where
  id := "SVG-LF-GRAMMAR"
  document := "docs/SVG-PACKAGE-PLAN.md"
  declarations := [`Whatwg.Svg.Value.CharSet, `Whatwg.Svg.Value.Syn, `Whatwg.Svg.Value.Regex,
    `Whatwg.Svg.Value.Grammar, `Whatwg.Svg.Value.Magnitude, `Whatwg.Svg.Value.Decimal,
    `Whatwg.Svg.Value.Point, `Whatwg.Svg.Value.Decimal.same_iff_reduce,
    `Whatwg.Svg.Value.Arc, `Whatwg.Svg.Value.Command, `Whatwg.Svg.Value.Path,
    `Whatwg.Svg.Value.PathData, `Whatwg.Svg.Value.Points, `Whatwg.Svg.Value.ViewBox,
    `Whatwg.Svg.Value.Transform, `Whatwg.Svg.Value.TransformList, `Whatwg.Svg.Value.LengthUnit,
    `Whatwg.Svg.Value.Length, `Whatwg.Svg.Value.Greedy, `Whatwg.Svg.Value.Syn.deterministic,
    `Whatwg.Svg.Value.Syn.run,
    `Whatwg.Svg.Value.Syn.explain]
  parent := some ("SVG-PG-SEAM", .representation)
  receipts := [
    .theorems [`Whatwg.Svg.Value.Syn.read_print, `Whatwg.Svg.Value.Syn.check_print,
      `Whatwg.Svg.Value.Syn.read_sound, `Whatwg.Svg.Value.Syn.print_matches,
      `Whatwg.Svg.Value.Grammar.read_print, `Whatwg.Svg.Value.Grammar.check_print,
      `Whatwg.Svg.Value.Grammar.print_injective, `Whatwg.Svg.Value.Grammar.matches_of_check,
      `Whatwg.Svg.Value.Decimal.isReduced_reduce, `Whatwg.Svg.Value.Decimal.reduce_of_isReduced,
      `Whatwg.Svg.Value.Decimal.same_reduce, `Whatwg.Svg.Value.Decimal.same_iff_reduce,
      `Whatwg.Svg.Value.Syn.greedy_iff_read, `Whatwg.Svg.Value.Syn.check_iff_greedy,
      `Whatwg.Svg.Value.Syn.read_complete, `Whatwg.Svg.Value.Syn.check_iff_matches,
      `Whatwg.Svg.Value.Syn.run_answer, `Whatwg.Svg.Value.Syn.explain_eq_none_iff,
      `Whatwg.Svg.Value.Syn.explain_le, `Whatwg.Svg.Value.Grammar.explain_print],
    .modules [`WhatwgTest.Svg.Grammar, `WhatwgTest.Svg.Number, `WhatwgTest.Svg.Path,
      `WhatwgTest.Svg.Points, `WhatwgTest.Svg.ViewBox, `WhatwgTest.Svg.Transform,
      `WhatwgTest.Svg.Length, `WhatwgTest.Svg.Greedy, `WhatwgTest.Svg.Deterministic,
      `WhatwgTest.Svg.Refusal]]

/-- The ledger: the twelve graphs of slices A and B and the graph
`SVG-PG-SEAM` of slice S3b of `docs/SVG-PACKAGE-PLAN.md` (ruling R-S9), the
two leaf records, and the fourteen unrouted prefixes of slice D (ruling
R-W22): the thirteen of debt D57, in the order of the contract's section 12,
and `Whatwg.Streams.Kernel`, of debt D68. The prefix `Whatwg.Svg` of debt
D78 (ruling R-S4) is gone: the fence of `SVG-PG-SEAM` owns its modules.
The rule banks of `Whatwg.Auto` (ruling R-S10) declare no constant that a
graph routes, so no prefix names them. -/
def ledger : Ledger where
  graphs := [dataQueue, promiseFirst, configurationOrdering, readableDefault, writableDefault,
    transformBackpressure, pipingForwardShutdown, infraUtf8, infraScalar, urlPercent, urlCensus,
    promiseAgent, svgSeam]
  leaves := [infraInteger, svgGrammar]
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
