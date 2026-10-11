import Whatwg.Html.Schema
import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.DecideBenchmark

Cost bounds (ruling HP-6): membership in the largest base and in a context
must be decided in a bounded number of heartbeats, because every
obligation of the typed tree is discharged this way at every node. The
generated membership functions are constructor dispatch, so each check is
a few delta and iota steps. `maxHeartbeats` is the gate.

## Whole-tree cost

The two probes below build a typed tree through the combinators and
measure the per-node bill: one admission per child, decided by the
`admits` tactic (compiled evaluation and a kernel-checked `Eq.refl`) and one
combined obligation per element (attributes and ordered model). Measured by
bisection on this pin, in thousands of heartbeats: deep 325/328, wide
448/453 (H7.3, before the obligations were merged: 350/355 and 486/489;
before the context-indexed core of H7: 256/259 and 434/437). The tactic reads a nested context by folding the compiled
`Ctx.child` over the chain rather than reducing it, which is what keeps a
deep tree linear. Bounds carry a margin. Finite probes.
-/

namespace WhatwgTest.Html.DecideBenchmark

open Whatwg.Html.Schema
open Whatwg.Html
open Whatwg.Html.Content (Ctx)

set_option maxHeartbeats 20 in
theorem flow_div : Bases.flow .div = true := by decide

set_option maxHeartbeats 20 in
theorem flow_head_false : Bases.flow .head = false := by decide

set_option maxHeartbeats 20 in
theorem nothing_empty_p : Bases.nothing .p = false := by decide

set_option maxHeartbeats 200 in
theorem admits_flow_div : Ctx.admits Ctx.flow .div = true := by decide

set_option maxHeartbeats 300 in
theorem admits_child : Ctx.admits (Ctx.child Ctx.phrasing .a) .em = true := by decide

set_option maxHeartbeats 20 in
theorem div_class : AttrSets.div_attrib .«class» = true := by decide

set_option maxHeartbeats 1200 in
/-- Sixteen nested `div`, then a `p` and a text run: eighteen nodes. -/
example : Element .div Ctx.flow := E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.p [E.txt "leaf"])])])])])])])])])])])])])])])])]

set_option maxHeartbeats 1800 in
/-- One `ul` with thirty `li`, each holding a text run: sixty-one nodes. -/
example : Element .ul Ctx.flow := E.ul [E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"])]

end WhatwgTest.Html.DecideBenchmark
