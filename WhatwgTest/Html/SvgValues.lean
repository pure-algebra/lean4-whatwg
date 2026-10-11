import Whatwg.Html
import WhatwgTest.Html.Svg

/-!
# WhatwgTest.Html.SvgValues

Readers, controls and finite evaluations of the judgment of SVG attribute values (slices S4b
and S4c of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-30): `Whatwg/Html/Content/Values.lean`, and
the run of a literal value in `html!` (`Whatwg/Html/Syntax/Elaborator.lean`).

The judgment is beside the checker, not inside it. A control here shows each side of that
line: a tree that `validIn` admits and `valuesOk` refuses, and a tree for the reverse.

What this battery does not claim: that `html!` proves a value. It runs the grammar on a
literal and refuses a bad one. The last section shows the route that is a proof: the text of a
typed value, by a theorem.
-/

namespace WhatwgTest.Html.SvgValues

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Svg.Value
open WhatwgTest.Html.Svg (el svg picture)

/-! ## The judgment -/

-- The consumer's picture holds three values with a grammar: a `viewBox`, a `d` and a
-- `transform`. Each is of its grammar, where the picture stands alone and in a paragraph.
#guard valuesOk picture && valuesOk (el "p" [] [picture])

/-- A path whose last command has an odd coordinate. -/
def badPath : RawNode := svg [el "path" [("d", "M 10 20 L 40")]]

-- Control: the checker admits the tree and the judgment refuses it. `validIn` reads no SVG
-- value.
#guard validIn Ctx.flow badPath && !valuesOk badPath

-- Controls: one bad value of each other grammar, each on an element that takes the attribute.
#guard !valuesOk (svg [el "polyline" [("points", "1 2 3")]])
#guard !valuesOk (el "svg" [("viewBox", "0 0 -10 10")])
#guard !valuesOk (svg [el "g" [("transform", "rotate(45deg)")]])
#guard !valuesOk (svg [el "linearGradient" [("gradientTransform", "skew(1)")]])
#guard !valuesOk (svg [el "pattern" [("patternTransform", "scale()")]])

-- An attribute with no grammar here takes any text. That is a limit of the package.
#guard valuesOk (svg [el "rect" [("x", "ten"), ("fill", "no colour"), ("class", "")]])

-- Control, the reverse: the judgment is of SVG elements. An HTML element's values are the
-- checker's, so an attribute named `d` on `p` passes here and is refused there.
#guard valuesOk (el "p" [("d", "not a path")]) && !validIn Ctx.flow (el "p" [("d", "not a path")])

-- The judgment reads the name and the value and not the element: a bad `d` on `rect` is
-- refused here, and the checker refuses the attribute there by its name.
#guard !valuesOk (svg [el "rect" [("d", "x")]]) && !validIn Ctx.flow (svg [el "rect" [("d", "M 0 0")]])

-- Below an integration point the namespace is HTML again, and in an `svg` below that it is
-- SVG again.
#guard valuesOk (svg [el "foreignObject" [] [el "p" [("points", "odd")]]])
#guard !valuesOk (svg [el "foreignObject" [] [el "p" [] [svg [el "polygon" [("points", "odd")]]]]])

/-! ## The located refusal -/

-- The path of the element whose value is refused, and the attribute.
#guard explainValues badPath == some ⟨[0], .attribute "d" .value⟩
#guard explainValues picture == none

-- The first bad value in document order: an element's own attributes, then its children.
#guard explainValues (el "svg" [("viewBox", "1 2 3")] [el "path" [("d", "L 1 1")]]) ==
  some ⟨[], .attribute "viewBox" .value⟩
#guard explainValues (svg [el "g" [] [el "path" [("d", "M 0 0")], el "path" [("d", "L 1 1")]]]) ==
  some ⟨[0, 1], .attribute "d" .value⟩

-- Reader: the refusal is absent exactly when the judgment holds.
example (n : RawNode) (h : explainValues n = none) : valuesOk n = true :=
  (explainValues_none_iff n).mp h

/-! ## `html!` runs a literal value -/

/-- An icon with a value of each grammar, as markup. The kernel takes seconds to open a
`String` as long as this path (ruling SV-30). The elaborator runs the path's grammar, and the
tree's obligation does not read it. -/
def icon : Child Ctx.flow :=
  html! <svg viewBox="0 0 24 24"><path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 \
    10-10S17.52 2 12 2zm0 3c1.66 0 3 1.34 3 3s-1.34 3-3 3-3-1.34-3-3 1.34-3 3-3zm0 14.2c-2.5 \
    0-4.71-1.28-6-3.22.03-1.99 4-3.08 6-3.08 1.99 0 5.97 1.09 6 3.08-1.29 1.94-3.5 3.22-6 \
    3.22z" /><g transform="translate(1,2) rotate(45)"><polygon points="0,0 1,0 1,1" /></g></svg>

#guard valuesOk icon.raw && validIn Ctx.flow icon.raw

/-- error: the value of the attribute `d` is not of its kind -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><path d="M 10 20 L 40" /></svg>

/-- error: the value of the attribute `viewBox` is not of its kind -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg viewBox="0 0 10"><rect /></svg>

/-- error: the value of the attribute `transform` is not of its kind -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><g transform="rotate(45deg)"></g></svg>

/-- error: the value of the attribute `points` is not of its kind -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><polyline points /></svg>

/-- A spliced value on an SVG element. -/
def traced (d : String) : Child Ctx.flow := html! <svg><path d={d} /></svg>

-- Control: the elaborator does not run a spliced value. The tree builds, and the judgment
-- refuses it.
#guard validIn Ctx.flow (traced "not a path").raw && !valuesOk (traced "not a path").raw

/-! ## A typed value needs no evaluation -/

-- Reader of `check_valueText`: the text of every typed path passes the check of `d`. The
-- value is not a literal, and nothing opens the text.
example (p : PathData) :
    valueOkByName "d".toList (valueText PathData.grammar p).toList = true :=
  valueOkByName_d p

-- The same through the walk: a tree that holds the text of any typed path and of any typed
-- transform list is of its grammars. The two equations of the root are evaluations of the
-- name `svg`; the rest is the walk's unfolding and the two laws.
example (p : PathData) (ts : TransformList) :
    valuesOk (svg [el "path" [("d", valueText PathData.grammar p),
      ("transform", valueText TransformList.grammar ts)]]) = true := by
  have hroot : Ns.valuesOk .html "svg" [] = true := by decide +kernel
  have hstep : Ns.step .html "svg" = .svg := by decide +kernel
  show valuesAt .html (.element "svg" [] [.element "path"
    [("d", valueText PathData.grammar p), ("transform", valueText TransformList.grammar ts)]
    []]) = true
  rw [valuesAt_element, hroot, hstep, valuesAllAt_cons, valuesAllAt_nil, valuesAt_element,
    valuesAllAt_nil, Ns.valuesOk_svg, svgValuesOk_cons, svgValuesOk_cons, svgValuesOk_nil,
    valueOkByName_d, valueOkByName_transform]
  rfl

end WhatwgTest.Html.SvgValues
