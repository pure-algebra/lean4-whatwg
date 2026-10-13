import Whatwg.Html.Node.Admit

/-!
# WhatwgTest.Html.AdmitBlind

An element that a function returns, placed where no attribute can change whether it is
admitted (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; the last part of entry W9 of
`docs/research/2026-10-12-whatwg-requests.md`): the tactic `admits` of
`Whatwg/Html/Node/Admit.lean`, on the law `Ctx.admitsWith_of_admits` of
`Whatwg/Html/Content/Monotone.lean`.

`E.el e` is `Child.of e` with the tactic as its default, so the forms below are the ones a
writer of a page meets. Before this slice the first two were left to the kernel, which stops
at the attributes of a variable: an `a` and an `input` have a category that reads an attribute.

A definition that elaborates is the test, and a rejection is pinned with its words.
-/

namespace WhatwgTest.Html.AdmitBlind

open Whatwg.Html
open Whatwg.Html.Schema (Tag)
open Whatwg.Html.Content (Ctx)

/-- A link that a function returns, among flow content. -/
def placed (link : Element .a Ctx.flow) : Child Ctx.flow := Child.of link (by admits)

/-- A control that a function returns, in a paragraph. -/
def control (input : Element .input (Ctx.flow.child .p)) : Child (Ctx.flow.child .p) :=
  Child.of input (by admits)

/-- A sheet that a function returns, in a head: metadata asks no condition of `link`. -/
def sheet (link : Element .link ((Ctx.document.child .html).child .head)) :
    Child ((Ctx.document.child .html).child .head) :=
  Child.of link (by admits)

-- Reader of `Ctx.admitsWith_of_admits`: what the tactic builds, for every attribute list.
example (attrs : List (String × String)) : Ctx.flow.admitsWith .a attrs = true :=
  Content.Ctx.admitsWith_of_admits _ _ _ (by decide) (by decide)

-- Control: inside a `button` an `a` is admitted only with no `href`, so a link whose
-- attributes are not written out is refused, and the words say why.
/--
error: <a> is not admitted here by its tag alone: the context is phrasing, excluding interactive content. Whether it is admitted reads its attributes, which are not written out
-/
#guard_msgs in
example (link : Element .a (Ctx.flow.child .button)) : Child (Ctx.flow.child .button) :=
  Child.of link (by admits)

-- Control: a `meta` is flow content only with `itemprop`. The answer reads its attributes.
/--
error: whether <meta> is admitted here reads its attributes, which are not written out: the context is flow
-/
#guard_msgs in
example (m : Element .meta Ctx.flow) : Child Ctx.flow := Child.of m (by admits)

-- Control: the law does not say more than the checker. With its `href` written out, the link
-- in a `button` is refused as before; with none it is admitted.
#guard !(Ctx.flow.child .button).admitsWith .a [("href", "/x")]
#guard (Ctx.flow.child .button).admitsWith .a []

end WhatwgTest.Html.AdmitBlind
