import Whatwg.Html.Content.Values
import Whatwg.Html.Content.Explain
-- Whatwg.Html.Content.Explain, which Whatwg.Html.Content.Values imports)

/-!
# WhatwgTest.Html.Describe

Finite evaluations, readers and controls of a refusal in words (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`; entry W7 of `docs/research/2026-10-12-whatwg-requests.md`): the end
of `Whatwg/Html/Content/Explain.lean`.

lean4-effect4 wrote these words itself (`describe`, `tools/Tools/Document/Html.lean`). That
function is restated here under its name, and the first guards hold the package's
`Refusal.describe` equal to it where a path has no `id`, no two elements of one name side by
side and no leaf at its end. The guards after them show what the package adds: an `id`, a
place among siblings, a leaf, and with `Refusal.describeIn` the words of the position.

The texts are the contract here: a guard holds each whole message.

What this battery does not claim: that a message names every fault of a tree. `explain`
answers the first refusal in document order.
-/

namespace WhatwgTest.Html.Describe

open Whatwg.Html
open Whatwg.Html.Content

def el (name : String) (attrs : List (String × String) := []) (children : List RawNode := []) :
    RawNode :=
  .element name attrs children

/-- The consumer's own words (`Tools.Document.Html.describe` of lean4-effect4): the element
names along the path, then the reason. -/
def consumerDescribe (tree : RawNode) (r : Refusal) : String :=
  let names := (List.range (r.path.length + 1)).filterMap fun k =>
    match tree.at? (r.path.take k) with
    | some (.element name _ _) => some name
    | _ => none
  "/" ++ "/".intercalate names ++ ": " ++ r.reason.describe

/-- A page around some content, with an `id` on `main` as the consumer's page has. -/
def page (content : List RawNode) : RawNode :=
  el "html" [("lang", "en")]
    [el "head" [] [el "title" [] [.text "t"]],
     el "body" [] [el "header" [] [el "h1" [] [.text "t"]], el "main" [("id", "content")] content]]

/-- The refusal of a page in the consumer's words, in the package's plain words, and in the
words of the position. -/
def theirs (tree : RawNode) : Option String :=
  (explain Ctx.document tree).map (consumerDescribe tree)
def plain (tree : RawNode) : Option String :=
  (explain Ctx.document tree).map fun refusal => refusal.describe tree
def words (tree : RawNode) : Option String := explainWords Ctx.document tree

/-! ## The port: the consumer's words, where a path is of plain names -/

def bare : RawNode :=
  el "html" [] [el "head" [] [el "title" [] [.text "t"]], el "body" [] [el "p" [] [el "div"]]]

#guard plain bare == some ("/html/body/p/div: " ++ Reason.describe .notAdmitted)
#guard plain bare == theirs bare

/-! ## What the package adds to the path -/

/-- A `div` in the second paragraph of a part. -/
def nested : RawNode :=
  page [el "section" [("id", "intro")]
    [el "h2" [] [.text "a"], el "p" [] [.text "x"], el "p" [] [.text "y", el "div"]]]

-- An `id` names its element, and a place among siblings of one name tells two paragraphs
-- apart. The consumer's words name neither.
#guard theirs nested == some ("/html/body/main/section/p/div: " ++ Reason.describe .notAdmitted)
#guard plain nested ==
  some ("/html/body/main#content/section#intro/p[2]/div: " ++ Reason.describe .notAdmitted)

-- A leaf is a step of the path. The consumer's words end at the list, as if it were refused.
#guard theirs (page [el "ul" [] [el "li", .text "loose"]]) ==
  some "/html/body/main/ul: character data may not stand here"
#guard plain (page [el "ul" [] [el "li", .text "loose"]]) ==
  some "/html/body/main#content/ul/text: character data may not stand here"

/-! ## The words of the position -/

-- The context that refuses an element: the words `html!` reports for the same markup.
#guard words nested ==
  some "/html/body/main#content/section#intro/p[2]/div: <div> is not admitted here: the context is phrasing"

-- The keywords an attribute takes.
#guard words (page [el "table" [] [el "thead" [] [el "tr" [] [el "th" [("scope", "column")] [.text "h"]]]]]) ==
  some "/html/body/main#content/table/thead/tr/th: attribute `scope` on <th> takes one of `row`, `col`, `rowgroup`, `colgroup`, not `column`"

-- An attribute that the element does not take, and one of no schema.
#guard words (page [el "p" [("href", "1")]]) ==
  some "/html/body/main#content/p: attribute `href` is not admitted on <p>: the attribute set `p_attrib` does not name it"
#guard words (page [el "p" [("nope", "1")]]) == some "/html/body/main#content/p: unknown attribute `nope`"

-- The model that the children break.
#guard words (page [el "figure" [] [el "p", el "figcaption", el "p"]]) ==
  some "/html/body/main#content/figure: the children of <figure> do not follow its content model: (figcaption (content-except-figcaption)* | ((content-except-figcaption)* figcaption | (content-except-figcaption)*))"

-- A text where none may stand, and the root itself.
#guard words (page [el "ul" [] [el "li", .text "loose"]]) ==
  some "/html/body/main#content/ul/text: text is not admitted here: the context is only_li"
#guard words (el "div") == some "/div: <div> is not admitted here: the context is document"

-- Inside an SVG subtree, and a name of no schema.
#guard words (page [el "p" [] [el "svg" [] [el "g" [] [el "rect"], el "feBlend"]]]) ==
  some "/html/body/main#content/p/svg/feBlend: <feBlend> is not admitted here, in the content of an SVG element"
#guard words (page [el "blink"]) == some "/html/body/main#content/blink: <blink> is no element of HTML"

-- A reason with no more to say keeps the words of `Reason.describe`.
#guard words (page [el "p" [("id", "a"), ("id", "b")]]) ==
  some "/html/body/main#content/p#a: an attribute name repeats"

-- A tree that the checker accepts has no words.
#guard words (page [el "p" [] [.text "x"]]) == none

/-! ## A refusal of another judgment, and a list -/

-- `Refusal.describe` reads no position, so it words the refusal of a value too.
#guard ((explainValues (page [el "p" [] [el "svg" [] [el "path" [("d", "M 0 x")]]]])).map fun r =>
    r.describe (page [el "p" [] [el "svg" [] [el "path" [("d", "M 0 x")]]]])) ==
  some "/html/body/main#content/p/svg/path: the value of the attribute `d` is not of its kind: no reading continues after 4 characters"

-- A refusal in a list of trees: the first step is the refused tree among the trees beside it.
#guard (ListRefusal.mk 2 ⟨[0], .notAdmitted⟩).describeIn (Ctx.flow.child .main)
    [el "p", el "p", el "p" [] [el "div"]] ==
  "/p[3]/div: <div> is not admitted here: the context is phrasing"

/-! ## The laws, at real trees -/

-- Reader of C5: the reason of the refusal of `nested` is the own reason of the node at its
-- path, at the position there.
example : ∃ q node, (Pos.html Ctx.document).at? nested [1, 1, 0, 2, 1] = some (q, node) ∧
    q.own? node = some .notAdmitted :=
  explainAt_own (.html Ctx.document) nested ⟨[1, 1, 0, 2, 1], .notAdmitted⟩ (by decide)

-- What that position is: phrasing content, in the HTML namespace, and the node is the `div`.
#guard ((Pos.html Ctx.document).at? nested [1, 1, 0, 2, 1]).map (fun found =>
    (found.1 == .html (Ctx.phrasing), found.2.tagName?)) == some (true, some "div")

-- Reader of `Pos.at?_node`: the node at a path does not depend on the position.
example (p : Pos) : (p.at? nested [1, 1]).map Prod.snd = nested.at? [1, 1] := Pos.at?_node _ p nested

-- Reader of `length_wordsAlong_of_explainAt`: the refusal of `nested` has six words.
example : (RawNode.wordsAlong [nested] [0, 1, 1, 0, 2, 1]).length = 6 :=
  length_wordsAlong_of_explainAt (.html Ctx.document) nested (r := ⟨[1, 1, 0, 2, 1], .notAdmitted⟩)
    (by decide)

-- Control: a path that leaves the tree has words as far as it goes, and no position.
#guard RawNode.wordsAlong [nested] [0, 1, 1, 9, 0] == ["html", "body", "main#content"]
#guard ((Pos.html Ctx.document).at? nested [1, 1, 9, 0]).isNone

-- Control: an empty `id` names nothing, and the place among siblings stands.
#guard RawNode.wordsAlong [el "ul" [] [el "li" [("id", "")], el "li" [("id", "")]]] [0, 1] ==
  ["ul", "li[2]"]

end WhatwgTest.Html.Describe
