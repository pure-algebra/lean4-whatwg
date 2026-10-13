import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Check
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Node.Run

/-!
# WhatwgTest.Html.Runs

The blocks of lean4-effect4's documents that stand under an ordered content model, written on
`Whatwg/Html/Node/Run.lean` (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entry W9 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at `6ad8f7b8d`:

| The consumer's code | Here |
| --- | --- |
| `algebra.fields`, `tools/Tools/Document/Html.lean`, line 78: a `dl` from rows that are data | `fields` |
| `algebra.code`, lines 80 to 91: a long statement folded in a `details` | `statement` |
| `algebra.graph`, line 113: the figure in words, a `details` | `words` |
| `head`, `tools/Tools/Site.lean`, lines 287 to 289: the head, once for each case of its styles | `head`, with the styles a run of their own |

The namespace `Theirs` restates the raw nodes that the consumer's fold writes; this module
imports nothing of that package. For each block a theorem says that the typed form erases to
the consumer's node, for every argument. The consumer checks these nodes when its program runs
(`Child.check`); the typed forms are checked when this module is compiled, for every row, every
body and every text.

What this battery does not claim: that this is the consumer's file. Its fold of a document, its
lines and its picture are not restated.
-/

namespace WhatwgTest.Html.Runs

open Whatwg.Html
open Whatwg.Html.Schema (Tag Seq)
open Whatwg.Html.Content (Ctx)

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- Where a block of a page stands. -/
abbrev InMain : Ctx := Ctx.document.below [.html, .body, .main]

/-! ## The consumer's nodes, as its fold writes them -/

namespace Theirs

/-- `algebra.fields`: a `dt` and a `dd` for each row. -/
def fields (rows : List (String × List RawNode)) : RawNode :=
  el "dl" (rows.flatMap fun row => [el "dt" [.text row.1], el "dd" row.2])

/-- The folded statement of `algebra.code`: its first line and its length in the summary, and
the block below. -/
def statement (first : String) (count : Nat) (block : RawNode) : RawNode :=
  el "details" [el "summary" [el "code" [.text (first ++ " …")], .text s!" ({count} lines)"], block]
    [("class", "statement")]

/-- The figure in words of `algebra.graph`: a line for each node. -/
def words (lines : List (List RawNode)) : RawNode :=
  el "details" [el "summary" [.text "The figure in words"], el "ul" (lines.map fun line => el "li" line)]
    [("class", "words")]

end Theirs

/-! ## Fields: a `dl` of any number of rows

The model of `dl` is groups of `dt` and `dd`. One group leads from the first state to a second
one, and from the second state back to it: so the first row is a run, and the others a loop. -/

/-- Where the value of a field stands. -/
abbrev InValue : Ctx := (InMain.child .dl).child .dd

/-- One field, from any state of the model: its label and its value. -/
def field {a : Seq} (row : String × List (Child InValue)) :
    Run InMain .dl a (Content.Seq.next .dl (Content.Seq.next .dl a .dt) .dd) :=
  (Run.el (E.dt [E.txt row.1])).append (Run.el (E.dd row.2))

/-- The fields, for every list of rows. -/
def fields : List (String × List (Child InValue)) → Element .dl InMain
  | [] => E.dl []
  | row :: rest => Element.ofRun ((field row).append (Run.loop (rest.map field)))

/-- The raw row of a typed row. -/
def erased (row : String × List (Child InValue)) : String × List RawNode :=
  (row.1, row.2.map Child.raw)

theorem loop_field_nodes {a : Seq} : ∀ rest : List (String × List (Child InValue)),
    ((rest.map (field (a := a))).map Run.nodes).flatten =
      (rest.map erased).flatMap fun row => [el "dt" [.text row.1], el "dd" row.2]
  | [] => rfl
  | row :: rest => by
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.map_cons, List.flatMap_cons,
      loop_field_nodes rest]
    rfl

/-- The typed fields erase to the consumer's node, for every list of rows. -/
theorem fields_toRaw : ∀ rows : List (String × List (Child InValue)),
    (fields rows).toRaw = Theirs.fields (rows.map erased)
  | [] => rfl
  | row :: rest => by
    have hnodes : (fields (row :: rest)).toRaw =
        el "dl" ([el "dt" [.text row.1], el "dd" (row.2.map Child.raw)] ++
          ((rest.map (field (a := _))).map Run.nodes).flatten) := rfl
    rw [hnodes, loop_field_nodes rest]
    rfl

-- No row, one row and three rows write the consumer's text.
#guard (fields []).render == "<dl></dl>"
#guard (fields [("claim", [E.txt "keys-once"])]).render == "<dl><dt>claim</dt><dd>keys-once</dd></dl>"
#guard (fields [("a", [E.txt "1"]), ("b", [E.txt "2"]), ("c", [E.txt "3"])]).render ==
  "<dl><dt>a</dt><dd>1</dd><dt>b</dt><dd>2</dd><dt>c</dt><dd>3</dd></dl>"

-- Control: the loop is found because a field leads from the second state back to it. A lone
-- label does not: after a `dt` the model waits for a `dd`, and a list of labels is refused.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Content.Seq.next Tag.dl (Content.Seq.start Tag.dl) Tag.dt = Content.Seq.start Tag.dl
is false
-/
#guard_msgs in
example (labels : List String) : Element .dl InMain :=
  Element.ofRun (Run.loop (labels.map fun label => Run.el (E.dt [E.txt label])))

/-! ## A `details`: a summary, then content that is data -/

/-- Where the content of a `details` stands: flow content, with the exclusions of its place. -/
abbrev InFold : Ctx := (InMain.child .details).rebase .flow

/-- A `details` of a class: its summary, and a body that is a variable. -/
def folded (className : String) (summary : List (Child ((InMain.child .details).child .summary)))
    (body : List (Child InFold)) : Element .details InMain :=
  Element.ofRun ((Run.el (E.summary summary)).append (Run.content .flow body)) [A.a_class className]

/-- A block of code in a language (`algebra.code`). -/
def codeBlock (language body : String) : Child InFold :=
  E.el (E.pre [E.el (E.code [E.txt body] [A.a_class ("language-" ++ language)])])

/-- A long statement, folded under its first line. -/
def statement (first : String) (count : Nat) (block : Child InFold) : Element .details InMain :=
  folded "statement" [E.el (E.code [E.txt (first ++ " …")]), E.txt s!" ({count} lines)"] [block]

/-- The figure in words: a line for each node. -/
def words (lines : List (List (Child ((InFold.child .ul).child .li)))) : Element .details InMain :=
  folded "words" [E.txt "The figure in words"] [E.el (E.ul (lines.map fun line => E.el (E.li line)))]

theorem statement_toRaw (first : String) (count : Nat) (block : Child InFold) :
    (statement first count block).toRaw = Theirs.statement first count block.raw := rfl

theorem items_raw : ∀ items : List (List (Child ((InFold.child .ul).child .li))),
    (items.map fun line => (E.el (E.li line) : Child (InFold.child .ul))).map Child.raw =
      (items.map fun line => line.map Child.raw).map fun line => el "li" line
  | [] => rfl
  | line :: rest => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, items_raw rest]
    rfl

theorem words_toRaw (lines : List (List (Child ((InFold.child .ul).child .li)))) :
    (words lines).toRaw = Theirs.words (lines.map fun line => line.map Child.raw) := by
  have hnodes : (words lines).toRaw =
      el "details" [el "summary" [.text "The figure in words"],
        el "ul" ((lines.map fun line => (E.el (E.li line) : Child (InFold.child .ul))).map Child.raw)]
        [("class", "words")] := rfl
  rw [hnodes, items_raw lines]
  rfl

#guard (statement "theorem complete_unique" 9 (codeBlock "lean" "theorem complete_unique : True")).render ==
  "<details class=\"statement\"><summary><code>theorem complete_unique …</code> (9 lines)</summary>" ++
    "<pre><code class=\"language-lean\">theorem complete_unique : True</code></pre></details>"

-- Content that was checked as flow content when the program ran goes into the fold as it is:
-- the body is a list of children of the content position.
#guard ((Child.checkAll? (ctx := InFold) [el "p" [.text "a"], el "ul" [el "li" [.text "b"]]]).map fun body =>
    (folded "note" [E.txt "More"] body).render) ==
  some "<details class=\"note\"><summary>More</summary><p>a</p><ul><li>b</li></ul></details>"

/-- The same in markup: the summary and the content are written with `html!`, each at the
position its place in the run gives it. -/
def note (body : List (Child InFold)) : Element .details InMain :=
  Element.ofRun ((Run.el (html! <summary>"More " <code>"x"</code></summary>)).append (Run.content .flow body))

#guard (note [html! <p>"a " <a href="#x">"link"</a></p>]).render ==
  "<details><summary>More <code>x</code></summary><p>a <a href=\"#x\">link</a></p></details>"

-- Control: a second summary is no content of a `details`. The content position refuses it,
-- where the position of the children of `details` would take it.
#guard (Child.check? (ctx := InFold) (el "summary" [.text "again"])).isNone
#guard (Child.check? (ctx := InMain.child .details) (el "summary" [.text "again"])).isSome

-- Control: before the summary the model does not take content. The test is false there.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Content.takes Tag.details (Content.Seq.start Tag.details) Schema.Base.flow = true
is false
-/
#guard_msgs in
example (body : List (Child InFold)) : Element .details InMain :=
  Element.ofRun ((Run.content .flow body).append (Run.el (E.summary [E.txt "Late"])))

-- Control: a run that stops before the model is satisfied is no element. An empty `details`
-- has no summary.
/--
error: could not synthesize default value for parameter 'hend' using tactics
---
error: Tactic `decide` proved that the proposition
  Content.Seq.nullable (Content.Seq.start Tag.details) = true
is false
-/
#guard_msgs in
example : Element .details InMain := Element.ofRun Run.nil

/-! ## The head: its fixed part once, and the styles a run -/

abbrev InHtml : Ctx := Ctx.document.child .html

/-- Where a page's styles stand (`Tools.Site.Styles`). -/
inductive Styles where
  | files (looks rules : String)
  | inlineLooks (looks : String) (rules : String)

namespace Theirs

/-- The head, as `Tools.Site.head` writes it in each case. -/
def head (tabTitle : String) : Styles → RawNode
  | .files looks rules =>
    el "head" [el "meta" [] [("charset", "utf-8")],
      el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      el "title" [.text tabTitle], el "link" [] [("rel", "stylesheet"), ("href", looks)],
      el "link" [] [("rel", "stylesheet"), ("href", rules)]]
  | .inlineLooks looks rules =>
    el "head" [el "meta" [] [("charset", "utf-8")],
      el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      el "title" [.text tabTitle], el "style" [.text looks],
      el "link" [] [("rel", "stylesheet"), ("href", rules)]]

end Theirs

/-- The state of the model of `head` after two `meta` elements and the title. -/
abbrev titled : Seq :=
  Content.Seq.next .head (Content.Seq.next .head (Content.Seq.next .head (Content.Seq.start .head) .meta) .meta)
    .title

/-- A linked sheet, which every state of `head` after its title takes and stays. -/
def sheet (href : String) : Run InHtml .head titled titled :=
  (Run.el (E.link [A.a_rel "stylesheet", A.a_href href])).cast

/-- The styles of a page, as a run after the title. -/
def styles : Styles → Run InHtml .head titled titled
  | .files looks rules => (sheet looks).append (sheet rules)
  | .inlineLooks looks rules => ((Run.el (E.style [E.txt looks])).cast).append (sheet rules)

/-- The head: the encoding, the viewport and the title are written once, and what follows the
title is a run that a function returns. -/
def headWith (tabTitle : String) (rest : Run InHtml .head titled titled) : Element .head InHtml :=
  Element.ofRun <|
    (Run.el (E.meta [A.a_charset "utf-8"])).append <|
    (Run.el (E.meta [A.a_name "viewport", A.a_content "width=device-width, initial-scale=1"])).append <|
    (Run.el (E.title [E.txt tabTitle])).append rest

def head (tabTitle : String) (s : Styles) : Element .head InHtml := headWith tabTitle (styles s)

/-- The head erases to the consumer's node in each case of the styles. -/
theorem head_toRaw (tabTitle : String) (s : Styles) : (head tabTitle s).toRaw = Theirs.head tabTitle s := by
  cases s <;> rfl

/-- The same head with any number of sheets: a list that is data, under an ordered model. -/
def headOf (tabTitle : String) (sheets : List String) : Element .head InHtml :=
  headWith tabTitle (Run.loop (sheets.map sheet))

#guard (headOf "T" ["a.css", "b.css"]).render ==
  "<head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
    "<title>T</title><link rel=\"stylesheet\" href=\"a.css\"><link rel=\"stylesheet\" href=\"b.css\"></head>"

-- Control: a second title after the first is refused: the state after the title does not take one.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Content.Seq.next Tag.head titled Tag.title = titled
is false
-/
#guard_msgs in
example (again : String) : Run InHtml .head titled titled := (Run.el (E.title [E.txt again])).cast

/-! ## Readers of the laws -/

-- Reader of `Run.append_assoc`: the head's children do not depend on how its runs are grouped.
example (tabTitle : String) (first second third : Run InHtml .head titled titled) :
    headWith tabTitle ((first.append second).append third) =
      headWith tabTitle (first.append (second.append third)) :=
  congrArg (headWith tabTitle) (Run.append_assoc first second third)

-- Reader of `Element.ofRun_toRun`: an element built by a combinator is its own run, closed.
example (e : Element .details InMain) :
    Element.ofRun e.toRun e.attrs e.hattrs (e.nullable_toRun (by decide) (by decide)) (by decide)
      e.htag = e :=
  Element.ofRun_toRun e _ _

-- Reader of `Run.check?_eq_some_iff`: raw nodes that enter a run are the run's nodes.
example (nodes : List RawNode) (r : Run InHtml .head titled titled)
    (h : Run.check? nodes = some r) : (headWith "T" r).children =
      (headWith "T" Run.nil).children ++ nodes := by
  rw [← Run.check?_eq_some_iff.mp h]
  rfl

-- Reader of `Content.Seq.matches_after_iff`: what the state after the title means. It matches
-- exactly the children that may still follow.
example (more : List Tag) :
    Content.Seq.Matches Tag.head.ownBase.contains
        (Content.Seq.after Tag.head.ownBase.contains (Content.Seq.start .head) [.meta, .meta, .title]) more ↔
      Content.Seq.Matches Tag.head.ownBase.contains (Content.Seq.start .head)
        ([.meta, .meta, .title] ++ more) :=
  Content.Seq.matches_after_iff _ _ _

end WhatwgTest.Html.Runs
