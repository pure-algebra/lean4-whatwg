import Whatwg.Html.Schema
import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.DecideBenchmark

The `decide` cost bound of slice H2 (`docs/HTML-PACKAGE-PLAN.md`, ruling
HP-6): membership in the largest content set, `flow`, and in the void set
must be decided by the kernel in a bounded number of heartbeats, because
every admission obligation of the typed tree (H3) is discharged this way at
every node of every document. The generated membership functions are
constructor dispatch, so each check is one delta step and one iota step.

`maxHeartbeats` is the gate: an elaboration that exceeds it fails the
build. The bound is deliberately tight; a regression of the emitter to a
list scan would exceed it. Every example is a finite probe, reported as
such: it is evidence about the cost of two reductions, not a theorem about
the content model.
-/

namespace WhatwgTest.Html.DecideBenchmark

open Whatwg.Html.Schema
open Whatwg.Html

set_option maxHeartbeats 20 in
theorem flow5_div : Sets.flow .div = true := by decide

set_option maxHeartbeats 20 in
theorem flow5_head_false : Sets.flow .head = false := by decide

set_option maxHeartbeats 20 in
theorem phrasing_span : Sets.phrasing .span = true := by decide

set_option maxHeartbeats 20 in
theorem phrasing_div_false : Sets.phrasing .div = false := by decide

set_option maxHeartbeats 20 in
theorem contains_flow5_p : ContentSet.contains .flow .p = true := by decide

set_option maxHeartbeats 20 in
theorem void_br : Tag.isVoid .br = true := by decide

set_option maxHeartbeats 20 in
theorem void_div_false : Tag.isVoid .div = false := by decide

set_option maxHeartbeats 20 in
theorem div_class : AttrSets.div_attrib .«class» = true := by decide

/-! The same check through the kernel-only route the census ruled for
kernel checks (`decide +kernel`). -/
set_option maxHeartbeats 20 in
theorem flow5_div_kernel : Sets.flow .div = true := by decide +kernel

/-! ## Whole-tree cost at H3.3–H3.4, remeasured after H4.1

The two probes below build a typed tree rather than deciding one membership,
so each measures the whole per-node bill of `Whatwg.Html.Node.Typed`: for
every child, one `Content.Admits` decided by `decide` after `childSet` has
resolved the context, and for every element, one `AttrsAdmitted` over its
(here empty) attribute list.

Measured on this pin by bisecting `maxHeartbeats` (the largest value that
still fails, then the smallest that passes), in the option's units of a
thousand heartbeats:

| Probe | Nodes | Fails at | Passes at | Bound set here |
| --- | --- | --- | --- | --- |
| deep: 15 nested `div`, then `p`, then a text run | 17 | 256 | 259 | 1200 |
| wide: one `ul` with 30 `li`, each holding a text run | 61 | 434 | 437 | 1800 |

At H3.4 the same probes failed at 350 and 550; the generated flat tables of
H4.1 took them to 317 and 522, and the `admits` tactic of
`Whatwg.Html.Node.Admit`, which evaluates each obligation with the compiled
schema and hands the kernel `Eq.refl true`, to the figures above. Where the cost goes, from
single-node probes with an empty file at about 10 as the baseline: one
combinator application with an empty attribute list costs about 9; one
`decide` on a closed admission about 6; and each unification of
`childSet set t` against the combinator's fixed content set, of which the
application elaborator performs three per `E.el`, about 10 the first time
and little afterwards, because `whnf` caches the closed term. The default
budget of 200 therefore holds a tree of roughly fifteen nested or fifty
flat element nodes; a larger construction through the combinators must
raise `maxHeartbeats`.

Four routes were measured and rejected at H4.1. `decide +kernel` on every
auto-parameter (356 and 567): the tactic is not the cost. `by exact rfl`
(445 and above 700): worse, since `decide` evaluates the `Decidable` instance
where `rfl` unifies at default transparency. A default value in place of the
tactic: impossible, because a default value is elaborated at the definition
site, where the set and tag are variables. And a cheaper `childSet`: the
generated `Tag.content?` and the per-set `Payloads` functions of H4.1 took
the resolver from a list walk and one 69-by-115 matcher to flat matches,
which is what moved the figures from 350 and 550, and nothing further is
left to flatten. The `admits` tactic then removed the `decide` reductions.
What remains, about six per combinator application, is the application
elaborator's own work, and that is why `html!` (H5) builds a document's
term directly, through the same compiled evaluation and kernel-checked
`Eq.refl` the tactic uses, rather than through these combinators.
Each bound carries roughly a threefold margin so that ordinary
machine-to-machine variation does not turn the gate red.

These are finite probes, reported as such: evidence about the cost of
elaborating two particular trees, not a theorem about the content model. -/

set_option maxHeartbeats 1200 in
/-- A tree nested fifteen `div` levels deep, with a `p` and a text run at the
bottom: seventeen nodes, seventeen admission obligations. -/
example : Element .div .flow :=
    E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el
    (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el
    (E.div [E.el (E.p [E.txt "leaf"])])])])])])])])])])])])])])])]

set_option maxHeartbeats 1800 in
/-- A wide tree: one `ul` with thirty `li`, each holding a text run. Sixty-one
nodes, sixty-one admission obligations. -/
example : Element .ul .only_li :=
    E.ul [E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]),
    E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el
    (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li
    [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"])]

end WhatwgTest.Html.DecideBenchmark
