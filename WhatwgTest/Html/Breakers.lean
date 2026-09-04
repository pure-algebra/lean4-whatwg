import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.Breakers

Negative probes for the combinators: constructions that must be REJECTED at
elaboration. `#check_failure` succeeds only when the term fails to elaborate,
and the `#guard_msgs` docstring above each one pins the exact diagnostic, so
a probe that started failing for a different reason would fail this file
rather than pass it silently. Each rejection is the auto-parameter `h` of
`E.el`/`E.txt` (admission) or `_ha` of a combinator (attributes), discharged
by the `admits` tactic of `Whatwg.Html.Node.Admit`, whose message names the
rejected element and describes the context.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Breakers

open Whatwg.Html
open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx)

/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: <div> is not admitted here: the context is phrasing
---
info: E.p [E.el (E.div [] [] ⋯ ⋯) ⋯] [] ⋯ ⋯ : Element Tag.p Ctx.flow
-/
#guard_msgs in
#check_failure (E.p [E.el (E.div [])] : Element .p Ctx.flow)

/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: <button> is not admitted here: the context is phrasing, excluding interactive content
---
info: E.p [E.el (E.button [E.el (E.button [] [] ⋯ ⋯) ⋯] [] ⋯ ⋯) ⋯] [] ⋯ ⋯ : Element Tag.p Ctx.flow
-/
#guard_msgs in
#check_failure (E.p [E.el (E.button [E.el (E.button [])])] : Element .p Ctx.flow)

/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: <div> is not admitted here: the context is phrasing, excluding interactive content, a
---
info: E.p [E.el (E.a [E.el (E.div [] [] ⋯ ⋯) ⋯] [] ⋯ ⋯) ⋯] [] ⋯ ⋯ : Element Tag.p Ctx.flow
-/
#guard_msgs in
#check_failure (E.p [E.el (E.a [E.el (E.div [])])] : Element .p Ctx.flow)

-- A descendant exclusion holds through a non-transparent element.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: <dfn> is not admitted here: the context is phrasing, excluding dfn
---
info: E.dfn [E.el (E.span [E.el (E.dfn [] [] ⋯ ⋯) ⋯] [] ⋯ ⋯) ⋯] [] ⋯ ⋯ : Element Tag.dfn Ctx.phrasing
-/
#guard_msgs in
#check_failure (E.dfn [E.el (E.span [E.el (E.dfn [])])] : Element .dfn Ctx.phrasing)

/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: text is not admitted here: the context is only_li
---
info: E.ul [E.txt "loose text" ⋯] [] ⋯ ⋯ : Element Tag.ul Ctx.flow
-/
#guard_msgs in
#check_failure (E.ul [E.txt "loose text"] : Element .ul Ctx.flow)

/--
info: could not synthesize default value for parameter '_ha' using tactics
---
info: attribute `href` is not admitted on <div>: the attribute set `div_attrib` does not name it
---
info: E.div [] [A.a_href "/target"] ⋯ ⋯ : Element Tag.div Ctx.flow
-/
#guard_msgs in
#check_failure (E.div [] [A.a_href "/target"] : Element .div Ctx.flow)

/--
info: could not synthesize default value for parameter '_ha' using tactics
---
info: attribute `dir` on <p> takes one of `ltr`, `rtl`, `auto`, not `lefty`
---
info: E.p [] [A.a_dir "lefty"] ⋯ ⋯ : Element Tag.p Ctx.flow
-/
#guard_msgs in
#check_failure (E.p [] [A.a_dir "lefty"] : Element .p Ctx.flow)

-- Rejected by `_hs`: the children of `html` must be `head` then `body`.
/--
info: could not synthesize default value for parameter '_hs' using tactics
---
info: the children of <html> do not follow its content model: head body
---
info: E.html [E.el (E.body [] [] ⋯ ⋯) ⋯, E.el (E.head [E.el (E.title [E.txt "t" ⋯] [] ⋯ ⋯) ⋯] [] ⋯ ⋯) ⋯] [] ⋯
  ⋯ : Element Tag.html Ctx.document
-/
#guard_msgs in
#check_failure (E.html [E.el (E.body []), E.el (E.head [E.el (E.title [E.txt "t"])])] : Element .html Ctx.document)

/--
info: could not synthesize default value for parameter '_hs' using tactics
---
info: the children of <table> do not follow its content model: (caption)? (colgroup)* (thead)? ((tbody)* | (tr)+) (tfoot)?
---
info: E.table [E.el (E.tfoot [] [] ⋯ ⋯) ⋯, E.el (E.caption [] [] ⋯ ⋯) ⋯] [] ⋯ ⋯ : Element Tag.table Ctx.flow
-/
#guard_msgs in
#check_failure (E.table [E.el (E.tfoot []), E.el (E.caption [])] : Element .table Ctx.flow)

-- `E.br` has no children parameter, so a list of children lands on `attrs`
-- and mismatches; the diagnostic mentions the recovery term and is not pinned.
#guard_msgs (drop info) in
#check_failure (E.br [E.txt "x"] : Element .br Ctx.phrasing)

end WhatwgTest.Html.Breakers
