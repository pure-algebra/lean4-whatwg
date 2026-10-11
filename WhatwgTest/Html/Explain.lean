import Whatwg.Html

/-!
# WhatwgTest.Html.Explain

Readers, controls and finite evaluations of the located refusal (slice S3c of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Html/Content/Explain.lean`. Each line builds a small tree
and evaluates `explain`, or applies `explain_none_iff` or `explainAt_path` at a real tree.

A finite evaluation here answers two things that no theorem states: which node is refused
first, and with which reason. A reader applies the completeness law in one direction at one
tree.

What this battery does not claim: that the first refusal is the only one in a tree.
-/

namespace WhatwgTest.Html.Explain

open Whatwg.Html
open Whatwg.Html.Content

/-- An element node. -/
def el (name : String) (attrs : List (String × String) := []) (children : List RawNode := []) :
    RawNode :=
  .element name attrs children

/-- The refusal of a tree at flow content. -/
def why (n : RawNode) : Option Refusal := explain Ctx.flow n

/-- The name of the node that a refusal's path leads to. -/
def refusedName (n : RawNode) : Option String := do
  let refusal ← why n
  let node ← n.at? refusal.path
  node.tagName?

/-! ## Each reason, at the node it names -/

-- A valid tree has no refusal.
#guard why (el "p" [] [.text "x", el "svg" [] [el "rect"]]) == none

-- The position does not admit the element: the path leads to the refused child.
#guard why (el "p" [] [.text "x", el "div"]) == some ⟨[1], .notAdmitted⟩
#guard refusedName (el "p" [] [.text "x", el "div"]) == some "div"

-- The same reason inside an SVG subtree, three levels down.
#guard why (el "div" [] [el "svg" [] [el "g" [] [el "rect"], el "div"]]) ==
  some ⟨[0, 1], .unknownElement⟩
#guard why (el "div" [] [el "svg" [] [el "g" [] [el "feBlend"]]]) == some ⟨[0, 0, 0], .notAdmitted⟩
#guard refusedName (el "div" [] [el "svg" [] [el "g" [] [el "feBlend"]]]) == some "feBlend"

-- A name of no schema, and a foreign element that is not modelled.
#guard why (el "blink") == some ⟨[], .unknownElement⟩
#guard why (el "math") == some ⟨[], .notModelled⟩

-- An attribute: no such name, not on this element, a value of the wrong kind, a repeat.
#guard why (el "p" [("nope", "x")]) == some ⟨[], .attribute "nope" .unknown⟩
#guard why (el "p" [("href", "x")]) == some ⟨[], .attribute "href" .notTaken⟩
#guard why (el "ol" [("start", "x")]) == some ⟨[], .attribute "start" .value⟩
#guard why (el "p" [("id", "a"), ("id", "b")]) == some ⟨[], .repeatedAttribute⟩
#guard why (el "svg" [("viewbox", "0 0 1 1")]) == some ⟨[], .attribute "viewbox" .unknown⟩
#guard why (el "svg" [] [el "rect" [("d", "M 0 0")]]) == some ⟨[0], .attribute "d" .notTaken⟩

-- The ordered model of an HTML element, and a count of an SVG one.
#guard why (el "figure" [] [el "svg", el "figcaption" [] [.text "x"], el "svg"]) ==
  some ⟨[], .order⟩
#guard why (el "svg" [] [el "filter" [] [el "feDiffuseLighting"]]) == some ⟨[0, 0], .count⟩

-- Character data and a comment where none may stand.
#guard why (el "svg" [] [.text "x"]) == some ⟨[0], .text⟩
#guard why (el "br" [] [.comment "c"]) == some ⟨[0], .comment⟩

-- The first refusal in document order is the one answered: the second child is refused too.
#guard why (el "p" [] [el "div", el "h1"]) == some ⟨[0], .notAdmitted⟩

-- A node's own reason comes before its children's: the element is refused, and so is a child.
#guard why (el "p" [("nope", "x")] [el "div"]) == some ⟨[], .attribute "nope" .unknown⟩

/-! ## The two laws, at real trees -/

-- Reader of C3: no refusal, so the checker accepts.
example : validIn Ctx.flow (el "p" [] [el "svg"]) = true :=
  (explain_none_iff Ctx.flow _).mp (by decide)

-- Reader of C3, the other way: the checker refuses, so a refusal exists.
example : explain Ctx.flow (el "p" [] [el "div"]) ≠ none :=
  fun h => absurd ((explain_none_iff Ctx.flow _).mp h) (by decide)

-- Reader of C4: the path of a refusal names a node of the tree.
example : ((el "div" [] [el "svg" [] [el "div"]]).at? [0, 0]).isSome = true :=
  explainAt_path (.html Ctx.flow) _ (r := ⟨[0, 0], .unknownElement⟩) (by decide)

-- Control: a path that leaves the tree names no node.
#guard ((el "p" [] [.text "x"]).at? [0, 0]).isNone && ((el "p").at? [3]).isNone

-- Every reason has its words.
#guard (Reason.describe (.attribute "d" .notTaken)) == "the element does not take the attribute `d`"

end WhatwgTest.Html.Explain