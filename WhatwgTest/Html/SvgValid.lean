import Whatwg.Html
import WhatwgTest.Html.SvgNode

/-!
# WhatwgTest.Html.SvgValid

Readers, controls and finite evaluations of the structure of a typed SVG tree (slices S6 and S7
of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-36): `Whatwg/Html/Node/SvgValid.lean`.

The trees are those of `WhatwgTest/Html/SvgNode.lean`: the shapes that lean4-effect4's picture
writer emits, built from variables. That battery shows that the values of every such picture
pass by the type. This one shows the other half: the structure of every such picture holds,
whatever its numbers and its texts, by one small evaluation, because `SvgNode.okAt` forces no
value. With the law `SvgNode.validIn_toRaw` the checker accepts the raw tree of each. The whole
fold of a consumer, from a list of device calls to a picture, is
`WhatwgTest/Html/SvgPicture.lean`.

A reader applies the law or an equation of `okAt` at a tree with free parts. A control is a
typed tree that `okAt` refuses, or a premise that cannot be dropped. A finite evaluation runs
`okAt` on a closed tree.

How a test is evaluated here. A closed test is `decide +kernel`. A test with free values is
`conv => lhs; whnf`: it reduces the test to `true` or `false` and stops at no value.

What this battery does not claim: that a browser draws a tree as intended.
-/

namespace WhatwgTest.Html.SvgValid

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Svg.Value
open WhatwgTest.Html.SvgNode (box curve label clipped picture chart note)

/-- Where the marks of a picture stand: below an outermost `svg` in flow content. -/
abbrev marks : Pos := Pos.belowSvg Ctx.flow

/-! ## The structure of a tree with free values -/

-- Readers of `okAt` at a tree whose numbers and texts are variables. The evaluation reads the
-- tags and the keys, and stops at no value.
example (x y : Int) (w h : Nat) (role key : String) :
    (box x y w h role key).okAt marks = true := by conv => lhs; whnf

example (p0 p1 p2 p3 : Int × Int) (role : String) :
    (curve p0 p1 p2 p3 role).okAt marks = true := by conv => lhs; whnf

example (x base ratio : Nat) (content : String) :
    (label x base ratio content).okAt marks = true := by conv => lhs; whnf

/-- A picture's structure holds for every look, size, ratio and list of marks, when each mark
passes where the marks stand. The proof is the equations of `okAt` and one evaluation of what
is closed. -/
theorem picture_ok (look : String) (W H ratio : Nat) (nodes : List SvgNode)
    (h : SvgNode.okAllAt marks nodes = true) :
    (picture look W H ratio nodes).okIn Ctx.flow = true := by
  rw [picture, SvgNode.okIn_svg, SvgNode.okAllAt_cons, h]
  conv => lhs; whnf

/-- A clipped group's structure holds when its children pass among the marks: the equation of
a group among the marks, `SvgNode.okAt_inSvg_g`, leaves its attributes and its children. -/
theorem clipped_ok (id : Nat) (x y : Int) (w h : Nat) (children : List SvgNode)
    (hc : SvgNode.okAllAt marks children = true) :
    SvgNode.okAllAt marks (clipped id x y w h children) = true := by
  rw [clipped, SvgNode.okAllAt_cons, SvgNode.okAllAt_cons, SvgNode.okAllAt_nil,
    SvgNode.okAt_inSvg_g, hc]
  conv => lhs; whnf

-- Reader of `Pos.belowElement_g` at two depths: a group in a group keeps the position, so the
-- children of the inner one stand where the marks stand.
example (children : List SvgNode) (h : SvgNode.okAllAt marks children = true) :
    (SvgNode.element .g [] [.element .g [] children]).okAt marks = true := by
  rw [SvgNode.okAt_inSvg_g, SvgNode.okAllAt_cons, SvgNode.okAt_inSvg_g, h]
  rfl

-- Control: `a` does not keep the position, since an `a` holds no `a`.
example :
    Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) (Ctx.flow.child .svg).excl .a
      ≠ marks := by
  decide +kernel

-- Reader of the law (V8) with `picture_ok`: the checker accepts the raw tree of a picture of
-- boxes, whatever the boxes hold. Nothing is evaluated here.
example (look : String) (W H ratio : Nat) (boxes : List (Int × Int × Nat × Nat × String)) :
    validIn Ctx.flow
      (picture look W H ratio
        (boxes.map fun b => box b.1 b.2.1 b.2.2.1 b.2.2.2.1 "a" b.2.2.2.2)).toRaw = true :=
  SvgNode.validIn_of_okIn (picture_ok look W H ratio _ ((SvgNode.okAllAt_iff _ _).mpr (by
    intro node hnode
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hnode
    conv => lhs; whnf)))

/-! ## A forest that a program builds -/

-- Reader of `okAllAt_map`: a mark for each item of a list passes when the mark of each does.
example (curves : List ((Int × Int) × (Int × Int) × (Int × Int) × (Int × Int))) :
    SvgNode.okAllAt marks (curves.map fun c => curve c.1 c.2.1 c.2.2.1 c.2.2.2 "ink") = true := by
  rw [SvgNode.okAllAt_map, List.all_eq_true]
  intro c _
  conv => lhs; whnf

-- Reader of `okAllAt_reverse` and `okAllAt_append`: a fold that gathers its marks last first,
-- before the marks it was given, loses nothing.
example (gathered before : List SvgNode) (hg : SvgNode.okAllAt marks gathered = true)
    (hb : SvgNode.okAllAt marks before = true) :
    SvgNode.okAllAt marks (gathered.reverse ++ before) = true := by
  rw [SvgNode.okAllAt_append, SvgNode.okAllAt_reverse, hg, hb]
  rfl

-- Reader of `okAllAt_flatMap` with `clipped_ok`: a clipped group for each item of a list.
example (groups : List (Nat × List SvgNode))
    (h : ∀ g ∈ groups, SvgNode.okAllAt marks g.2 = true) :
    SvgNode.okAllAt marks (groups.flatMap fun g => clipped g.1 0 0 10 10 g.2) = true := by
  rw [SvgNode.okAllAt_flatMap, List.all_eq_true]
  intro g hg
  exact clipped_ok g.1 0 0 10 10 g.2 (h g hg)

-- Reader of `tags_append`: the tags that a count reads are those of the two parts.
example (nodes : List SvgNode) :
    SvgNode.tags (nodes ++ [.element .title [] []]) = SvgNode.tags nodes ++ [.title] :=
  SvgNode.tags_append nodes _

/-! ## A closed tree -/

-- The structure of a closed typed tree is one evaluation over tags and keys.
example : chart.okIn Ctx.flow = true := by decide +kernel

-- Reader of the law at a closed tree: the checker's verdict is `okIn`'s.
example : validIn Ctx.flow chart.toRaw = chart.okIn Ctx.flow := SvgNode.validIn_toRaw _ _

/-! ## A typed picture in a typed document -/

/-- A typed SVG tree in the typed HTML tree: a child of flow content. -/
def figure : Child Ctx.flow := Child.ofSvg chart

example : figure.raw = chart.toRaw := rfl

/-- The picture in a paragraph: a child of a generated combinator. Its premise is the default
one, an evaluation of `okIn` where the paragraph's children stand. -/
def inParagraph : Element .p Ctx.flow := E.p [Child.ofSvg chart]

/-- The picture in a figure with its caption: a combinator whose content model has an order. -/
def captioned : Element .figure Ctx.flow :=
  E.figure [Child.ofSvg chart, E.el (E.figcaption [E.txt "A chart"])]

/-- The picture spliced into markup. -/
def inMarkup : Element .p Ctx.flow := html! <p>{Child.ofSvg chart}</p>

/-- A picture that is a variable, with its proof: nothing is evaluated. -/
def placed (node : SvgNode) (h : node.okIn (Ctx.flow.child .p) = true) : Element .p Ctx.flow :=
  E.p [Child.ofSvg node h]

-- The typed HTML tree prints the typed SVG tree.
#guard (E.p [Child.ofSvg (.element .svg [] [.element .rect [.attr .width 30] []])]
    : Element .p Ctx.flow).render == "<p><svg><rect width=\"30\"></rect></svg></p>"
#guard inParagraph.render == inMarkup.render

-- A typed tree that passes is a document of the checker at its position.
example : (chart.toDoc (ctx := Ctx.flow)).val = chart.toRaw := rfl

-- A typed tree is shown as its raw tree.
#guard reprStr (SvgNode.element .rect [.attr .x 10] []) ==
  reprStr (SvgNode.element .rect [.attr .x 10] []).toRaw

/-! ## What the test refuses -/

-- Control: an element where the content model refuses it. `path` is no child of `rect`.
example : (SvgNode.element .svg [] [.element .rect [] [.element .path [] []]]).okIn Ctx.flow
    = false := by decide +kernel

-- Control: an attribute its element does not take. `d` is no attribute of `rect`.
example (p : PathData) : (SvgNode.element .rect [.attr .d p] []).okAt marks = false := by
  conv => lhs; whnf

-- Control: a key that repeats, whatever the two values are.
example (a b : String) :
    (SvgNode.element .rect [.attr .«class» a, .attr .«class» b] []).okAt marks = false := by
  conv => lhs; whnf

-- Control: a custom data attribute whose key has an upper-case letter.
example (v : String) : (SvgNode.element .rect [.data "Key" v] []).okAt marks = false := by
  conv => lhs; whnf

-- Control: the premise of `picture_ok` stands. A mark that does not pass refuses the picture.
example : (picture "plain" 1 1 1 [.element .rect [] [.element .path [] []]]).okIn Ctx.flow
    = false := by decide +kernel

-- Control: an SVG element that is not `svg` has no place in flow content.
example : (SvgNode.element .rect [] []).okIn Ctx.flow = false := by decide +kernel

-- Control: a line break among the marks is character data, which `svg` does not take. A
-- typed picture is written on one line.
example : (SvgNode.text "\n").okAt marks = false := by decide +kernel

/-! ## Below an integration point -/

-- The HTML content below `foreignObject` is a raw subtree, which the checker judges inside
-- the one evaluation.
example : note.okIn Ctx.flow = true := by decide +kernel

-- Control: a raw subtree that the checker refuses refuses the tree. A `p` holds no `div`.
example : (SvgNode.element .svg []
    [.element .foreignObject []
      [.raw (.element "p" [] [.element "div" [] []]) (by decide +kernel)]]).okIn Ctx.flow
    = false := by decide +kernel

-- A nested `svg` below an integration point is the foreign root again.
example : (SvgNode.element .svg []
    [.element .foreignObject [] [.element .svg [] [.element .rect [] []]]]).okIn Ctx.flow
    = true := by decide +kernel

end WhatwgTest.Html.SvgValid
