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
`docs/SVG-PACKAGE-PLAN.md` and the grammars of slices S4b to S5, each an exact
representation whose laws the library proves once, with the reader's rule as a relation, its
bridge to the expression's language and the located refusal of a text. Since slice S10 it also
holds the geometry on those values: exact arithmetic, the cursor of a path with the pen, and
a transform on a point. Since slice S11 it holds the exact geometry in `Rat`: the number of a
value, a cubic segment, a box, an affine map, outlines, a root, the curves of d3-shape as
segments, and the writer of segments. Since slice S12 it holds the layer with no rational
number, `Whatwg.Svg.Scene` (things that move, the join by key, motion as data), the seam
between whole units and exact numbers, and a stroke of varying width. It contributes to the representation edge of
`SVG-PG-SEAM`. -/
def svgGrammar : Leaf where
  id := "SVG-LF-GRAMMAR"
  document := "docs/SVG-PACKAGE-PLAN.md"
  declarations := [`Whatwg.Svg.Value.CharSet, `Whatwg.Svg.Value.Syn, `Whatwg.Svg.Value.Regex,
    `Whatwg.Svg.Value.Grammar, `Whatwg.Svg.Value.Syn.read_print, `Whatwg.Svg.Value.Magnitude,
    `Whatwg.Svg.Value.Decimal,
    `Whatwg.Svg.Value.Point, `Whatwg.Svg.Value.Decimal.same_iff_reduce,
    `Whatwg.Svg.Value.Arc, `Whatwg.Svg.Value.Command, `Whatwg.Svg.Value.Path,
    `Whatwg.Svg.Value.PathData, `Whatwg.Svg.Value.Points, `Whatwg.Svg.Value.ViewBox,
    `Whatwg.Svg.Value.Transform, `Whatwg.Svg.Value.TransformList, `Whatwg.Svg.Value.LengthUnit,
    `Whatwg.Svg.Value.Length, `Whatwg.Svg.Value.Extent, `Whatwg.Svg.Value.AutoExtent,
    `Whatwg.Svg.Value.LengthList, `Whatwg.Svg.Value.NumberList,
    `Whatwg.Svg.Value.Greedy, `Whatwg.Svg.Value.Syn.deterministic,
    `Whatwg.Svg.Value.Syn.run,
    `Whatwg.Svg.Value.Syn.explain,
    `Whatwg.Svg.Value.Decimal.fixed, `Whatwg.Svg.Value.Decimal.mul_add,
    `Whatwg.Svg.Value.Decimal.compare, `Whatwg.Svg.Value.AutoExtent.clamp,
    `Whatwg.Svg.Value.Decimal.add_same, `Whatwg.Svg.Value.Cursor, `Whatwg.Svg.Value.Pen,
    `Whatwg.Svg.Value.Pen.cursor_path, `Whatwg.Svg.Value.Curve,
    `Whatwg.Svg.Value.Curve.chained_cubics, `Whatwg.Svg.Value.Matrix,
    `Whatwg.Svg.Value.Matrix.apply_mul,
    `Whatwg.Svg.Value.Vec, `Whatwg.Svg.Value.Decimal.toRat,
    `Whatwg.Svg.Value.Decimal.same_iff_toRat, `Whatwg.Svg.Value.Cubic,
    `Whatwg.Svg.Value.Cubic.between_pointAt, `Whatwg.Svg.Value.Box,
    `Whatwg.Svg.Value.Affine, `Whatwg.Svg.Value.Cubic.roundRect,
    `Whatwg.Svg.Value.Cubic.roundRect_within, `Whatwg.Svg.Value.sqrtDown,
    `Whatwg.Svg.Value.sqrtDown_mul_self_le, `Whatwg.Svg.Value.Pen.cubic,
    `Whatwg.Svg.Scene.IVec, `Whatwg.Svg.Scene.Moves, `Whatwg.Svg.Scene.join,
    `Whatwg.Svg.Scene.join_new, `Whatwg.Svg.Scene.Easing, `Whatwg.Svg.Scene.Track,
    `Whatwg.Svg.Scene.Track.at_done, `Whatwg.Svg.Value.Vec.toGrid_add_ofGrid,
    `Whatwg.Svg.Scene.Easing.segment_pointAt, `Whatwg.Svg.Value.Curve.smooth_windows,
    `Whatwg.Svg.Value.Cubic.written_near, `Whatwg.Svg.Value.Noise.two_band,
    `Whatwg.Svg.Value.Stroke.stroke, `Whatwg.Svg.Value.Stroke.stroke_move,
    `Whatwg.Svg.Value.stack, `Whatwg.Svg.Scene.Tree, `Whatwg.Svg.Scene.Kept,
    `Whatwg.Svg.Scene.Share, `Whatwg.Svg.Scene.Motion.Respects]
  parent := some ("SVG-PG-SEAM", .representation)
  receipts := [
    .theorems [`Whatwg.Svg.Value.Syn.read_print, `Whatwg.Svg.Value.Syn.check_print,
      `Whatwg.Svg.Value.Syn.read_sound, `Whatwg.Svg.Value.Syn.print_matches,
      `Whatwg.Svg.Value.Grammar.read_print, `Whatwg.Svg.Value.Grammar.check_print,
      `Whatwg.Svg.Value.Grammar.print_injective, `Whatwg.Svg.Value.Grammar.matches_of_check,
      `Whatwg.Svg.Value.Decimal.isReduced_reduce, `Whatwg.Svg.Value.Decimal.reduce_of_isReduced,
      `Whatwg.Svg.Value.Decimal.same_reduce, `Whatwg.Svg.Value.Decimal.same_iff_reduce,
      `Whatwg.Svg.Value.Decimal.same_trim, `Whatwg.Svg.Value.Decimal.trim_exponent_nonpos,
      `Whatwg.Svg.Value.Magnitude.ofInt?_of_nonneg, `Whatwg.Svg.Value.Magnitude.ofInt?_of_neg,
      `Whatwg.Svg.Value.Path.ofSubpaths_singleton,
      `Whatwg.Svg.Value.Syn.greedy_iff_read, `Whatwg.Svg.Value.Syn.check_iff_greedy,
      `Whatwg.Svg.Value.Syn.read_complete, `Whatwg.Svg.Value.Syn.check_iff_matches,
      `Whatwg.Svg.Value.Syn.run_answer, `Whatwg.Svg.Value.Syn.explain_eq_none_iff,
      `Whatwg.Svg.Value.Syn.explain_le, `Whatwg.Svg.Value.Grammar.explain_print,
      `Whatwg.Svg.Value.Syn.run_local, `Whatwg.Svg.Value.Syn.explain_local,
      `Whatwg.Svg.Value.Grammar.explain_local,
      `Whatwg.Svg.Value.Extent.print_eq_length,
      `Whatwg.Svg.Value.Decimal.add_assoc, `Whatwg.Svg.Value.Decimal.mul_assoc,
      `Whatwg.Svg.Value.Decimal.mul_add, `Whatwg.Svg.Value.Decimal.add_same,
      `Whatwg.Svg.Value.Decimal.mul_same, `Whatwg.Svg.Value.Decimal.roundQuotient_bound,
      `Whatwg.Svg.Value.Decimal.compare_eq_iff_same, `Whatwg.Svg.Value.Decimal.le_trans,
      `Whatwg.Svg.Value.Decimal.le_total, `Whatwg.Svg.Value.Decimal.add_le_add_right,
      `Whatwg.Svg.Value.Path.cursor_ofSubpaths_append, `Whatwg.Svg.Value.Pen.cursor_path,
      `Whatwg.Svg.Value.Matrix.apply_mul,
      `Whatwg.Svg.Value.TransformList.image?_append,
      `Whatwg.Svg.Value.PanZoom.image?_toList, `Whatwg.Svg.Value.PanZoom.apply_andThen,
      `Whatwg.Svg.Value.Decimal.toRat_add, `Whatwg.Svg.Value.Decimal.toRat_mul,
      `Whatwg.Svg.Value.Decimal.same_iff_toRat, `Whatwg.Svg.Value.Decimal.le_iff_toRat,
      `Whatwg.Svg.Value.Decimal.ofRat_div_pow, `Whatwg.Svg.Value.Decimal.toRat_ofRat_le,
      `Whatwg.Svg.Value.Vec.round_fixed,
      `Whatwg.Svg.Value.Cubic.between_pointAt, `Whatwg.Svg.Value.Cubic.map_pointAt,
      `Whatwg.Svg.Value.Cubic.between_velocity, `Whatwg.Svg.Value.Box.contains_lerp,
      `Whatwg.Svg.Value.Cubic.contains_pointAt, `Whatwg.Svg.Value.Cubic.includes_between,
      `Whatwg.Svg.Value.Affine.apply_mul, `Whatwg.Svg.Value.Affine.inverse_apply,
      `Whatwg.Svg.Value.Affine.normSq_turn, `Whatwg.Svg.Value.Cubic.transform_pointAt,
      `Whatwg.Svg.Value.TransformList.toVec_image?,
      `Whatwg.Svg.Value.Cubic.closed_roundRect, `Whatwg.Svg.Value.Cubic.roundRect_within,
      `Whatwg.Svg.Value.sqrtDown_mul_self_le, `Whatwg.Svg.Value.lt_sqrtDown_succ,
      `Whatwg.Svg.Value.Vec.dist_move, `Whatwg.Svg.Value.Cubic.offsetAt_move,
      `Whatwg.Svg.Value.Pen.current_cubic, `Whatwg.Svg.Value.Pen.done_cubics,
      `Whatwg.Svg.Value.Path.endPoint_ofCubics,
      `Whatwg.Svg.Value.Curve.chained_cubics, `Whatwg.Svg.Value.Curve.cubics_last,
      `Whatwg.Svg.Value.Curve.cardinal_starts, `Whatwg.Svg.Value.Curve.closed_cubicsClosed,
      `Whatwg.Svg.Value.Curve.cubics_move, `Whatwg.Svg.Value.Shape.endPoint_line,
      `Whatwg.Svg.Scene.Commutes.stored, `Whatwg.Svg.Scene.Commutes.from_origin,
      `Whatwg.Svg.Scene.Commutes.transport, `Whatwg.Svg.Scene.join_new,
      `Whatwg.Svg.Scene.join_old, `Whatwg.Svg.Scene.length_enter_add_update,
      `Whatwg.Svg.Scene.mem_update_iff, `Whatwg.Svg.Scene.Easing.stopsAt_stop,
      `Whatwg.Svg.Scene.Easing.proper_cubic, `Whatwg.Svg.Scene.Transition.at_done,
      `Whatwg.Svg.Scene.Track.at_done, `Whatwg.Svg.Scene.Motion.within_atRest,
      `Whatwg.Svg.Scene.Motion.length_arrive, `Whatwg.Svg.Scene.Motion.arrive_end,
      `Whatwg.Svg.Value.Vec.toGrid_ofGrid, `Whatwg.Svg.Value.Vec.toGrid_add_ofGrid,
      `Whatwg.Svg.Value.Vec.snap_add_ofGrid, `Whatwg.Svg.Scene.Commutes.grid,
      `Whatwg.Svg.Value.mix_eq_floor, `Whatwg.Svg.Scene.Easing.segment_pointAt,
      `Whatwg.Svg.Scene.Easing.cubicAt_eq_floor, `Whatwg.Svg.Value.Curve.smooth_windows,
      `Whatwg.Svg.Value.Curve.smooth_cubics_cardinal, `Whatwg.Svg.Value.Cubic.pointAt_near,
      `Whatwg.Svg.Value.Cubic.written_near, `Whatwg.Svg.Value.Cubic.chord_error,
      `Whatwg.Svg.Value.Noise.two_band, `Whatwg.Svg.Value.Stroke.closed_stroke,
      `Whatwg.Svg.Value.Stroke.stroke_move, `Whatwg.Svg.Value.Stroke.organic_band,
      `Whatwg.Svg.Value.Stroke.commutes_onGrid, `Whatwg.Svg.Value.Curve.through_move,
      `Whatwg.Svg.Value.stack_lengths, `Whatwg.Svg.Value.stack_apart,
      `Whatwg.Svg.Value.ports_move, `Whatwg.Svg.Scene.Easing.cubicOf_eq_floor,
      `Whatwg.Svg.Scene.Transition.at_cubic, `Whatwg.Svg.Scene.Tree.spans_within,
      `Whatwg.Svg.Scene.Tree.spansAll_apart, `Whatwg.Svg.Scene.Tree.spans_shift,
      `Whatwg.Svg.Scene.Tree.spans_values, `Whatwg.Svg.Scene.Easing.of_thousand,
      `Whatwg.Svg.Scene.mix_shift, `Whatwg.Svg.Scene.ICubic.mix_move,
      `Whatwg.Svg.Scene.Change.at_morph, `Whatwg.Svg.Scene.Motion.length_arriveWith,
      `Whatwg.Svg.Scene.Motion.arriveWith_end, `Whatwg.Svg.Scene.Motion.delayed_within_atRest,
      `Whatwg.Svg.Scene.mix_gap, `Whatwg.Svg.Scene.mix_mem,
      `Whatwg.Svg.Scene.Easing.bounded_at, `Whatwg.Svg.Scene.Transition.bounded_at,
      `Whatwg.Svg.Scene.Kept.moment, `Whatwg.Svg.Scene.grow_clear,
      `Whatwg.Svg.Scene.rootDown_pow_le, `Whatwg.Svg.Scene.lt_rootDown_succ_pow,
      `Whatwg.Svg.Scene.Motion.finish_le, `Whatwg.Svg.Scene.Motion.delayed_respects,
      `Whatwg.Svg.Scene.Motion.reduced_settles, `Whatwg.Svg.Scene.Motion.fit_finish],
    .modules [`WhatwgTest.Svg.Grammar, `WhatwgTest.Svg.Number, `WhatwgTest.Svg.Path,
      `WhatwgTest.Svg.Points, `WhatwgTest.Svg.ViewBox, `WhatwgTest.Svg.Transform,
      `WhatwgTest.Svg.Length, `WhatwgTest.Svg.Extent, `WhatwgTest.Svg.Lists,
      `WhatwgTest.Svg.Greedy,
      `WhatwgTest.Svg.Deterministic,
      `WhatwgTest.Svg.Refusal, `WhatwgTest.Svg.D3Shape]]

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
