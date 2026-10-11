import Whatwg.Html
import WhatwgTest.Html.Svg

/-!
# WhatwgTest.Html.SvgValues

Readers, controls and finite evaluations of the judgment of SVG attribute values (slices S4b
to S4d of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-30): `Whatwg/Html/Content/Values.lean`, and
the run of a literal value in `html!` (`Whatwg/Html/Syntax/Elaborator.lean`).

The judgment is beside the checker, not inside it. A control here shows each side of that
line: a tree that `validIn` admits and `valuesOk` refuses, and a tree for the reverse. A
refusal names the offset in the value at which no reading continues, and one line shows that
the offset is the furthest character a reading reached.

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

-- Controls: one bad value of each other kind, each on an element that takes the attribute.
#guard !valuesOk (svg [el "polyline" [("points", "1 2 3")]])
#guard !valuesOk (el "svg" [("viewBox", "0 0 -10 10")])
#guard !valuesOk (svg [el "g" [("transform", "rotate(45deg)")]])
#guard !valuesOk (svg [el "linearGradient" [("gradientTransform", "skew(1)")]])
#guard !valuesOk (svg [el "pattern" [("patternTransform", "scale()")]])

-- The four coordinates of `line` are lengths: a number, a unit of the sealed table in either
-- case, a percentage, and white space at both ends.
#guard valuesOk (svg [el "line" [("x1", "0"), ("y1", "1.5em"), ("x2", "50%"), ("y2", " 10PX ")]])
#guard validIn Ctx.flow (svg [el "line" [("x1", "0"), ("y1", "1.5em")]])

-- Controls: white space before the unit, and a unit the sealed table does not name. The second
-- is a length of CSS, and this package refuses it: CSS Values is not sealed (ruling SV-31).
#guard !valuesOk (svg [el "line" [("x1", "10 px")]])
#guard !valuesOk (svg [el "line" [("x1", "10rem")]])

-- Control of the table's key: `x1` has a kind on `line` alone. On `linearGradient` its
-- definition is in a chapter that is not sealed, and the value is not judged (ruling SV-32).
#guard valuesOk (svg [el "linearGradient" [("x1", "ten")]])

-- An attribute with no kind takes any text. That is a limit of the package: the geometry
-- properties are lengths in SVG, and their chapter is not sealed.
#guard valuesOk (svg [el "rect" [("x", "ten"), ("fill", "no colour"), ("class", "")]])

-- Control, the reverse: the judgment is of SVG elements. An HTML element's values are the
-- checker's, so an attribute named `d` on `p` passes here and is refused there.
#guard valuesOk (el "p" [("d", "not a path")]) && !validIn Ctx.flow (el "p" [("d", "not a path")])

-- `d` has one grammar wherever it stands: a bad `d` on `rect` is refused here, and the checker
-- refuses the attribute there by its name. An element of no schema has no kind for any name.
#guard !valuesOk (svg [el "rect" [("d", "x")]]) && !validIn Ctx.flow (svg [el "rect" [("d", "M 0 0")]])
#guard valuesOk (svg [el "blob" [("d", "x")]]) && !validIn Ctx.flow (svg [el "blob" [("d", "x")]])

-- Below an integration point the namespace is HTML again, and in an `svg` below that it is
-- SVG again.
#guard valuesOk (svg [el "foreignObject" [] [el "p" [("points", "odd")]]])
#guard !valuesOk (svg [el "foreignObject" [] [el "p" [] [svg [el "polygon" [("points", "odd")]]]]])

/-! ## The located refusal -/

-- The path of the element whose value is refused, the attribute, and the offset in the value
-- at which no reading continues. Here the value ends where a coordinate must follow.
#guard explainValues badPath == some ⟨[0], .attribute "d" (.valueAt 12)⟩
#guard explainValues picture == none

-- The offset is the furthest character a reading reached, not where the reader stopped: the
-- reader gives up the whole `L` command, and the fault is the `x` after its first coordinate.
#guard explainValues (svg [el "path" [("d", "M 10 20 L 40 x")]]) ==
  some ⟨[0], .attribute "d" (.valueAt 13)⟩
#guard explainValues (svg [el "line" [("x1", "10 px")]]) == some ⟨[0], .attribute "x1" (.valueAt 3)⟩

-- The first bad value in document order: an element's own attributes, then its children.
#guard explainValues (el "svg" [("viewBox", "1 2 3")] [el "path" [("d", "L 1 1")]]) ==
  some ⟨[], .attribute "viewBox" (.valueAt 5)⟩
#guard explainValues (svg [el "g" [] [el "path" [("d", "M 0 0")], el "path" [("d", "L 1 1")]]]) ==
  some ⟨[0, 1], .attribute "d" (.valueAt 0)⟩

-- Reader: the refusal is absent exactly when the judgment holds.
example (n : RawNode) (h : explainValues n = none) : valuesOk n = true :=
  (explainValues_none_iff n).mp h

-- The message of a refusal.
#guard (Reason.attribute "d" (.valueAt 12)).describe ==
  "the value of the attribute `d` is not of its kind: no reading continues after 12 characters"

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

/-- error: the value of the attribute `d` is not of its kind: no reading continues after 12 characters -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><path d="M 10 20 L 40" /></svg>

/-- error: the value of the attribute `viewBox` is not of its kind: no reading continues after 6 characters -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg viewBox="0 0 10"><rect /></svg>

/-- error: the value of the attribute `transform` is not of its kind: no reading continues after 9 characters -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><g transform="rotate(45deg)"></g></svg>

/-- error: the value of the attribute `points` is not of its kind: no reading continues after 0 characters -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><polyline points /></svg>

/-- A spliced value on an SVG element. -/
def traced (d : String) : Child Ctx.flow := html! <svg><path d={d} /></svg>

-- Control: the elaborator does not run a spliced value. The tree builds, and the judgment
-- refuses it.
#guard validIn Ctx.flow (traced "not a path").raw && !valuesOk (traced "not a path").raw

/-! ## A typed value needs no evaluation -/

-- Reader of `valueOkByName_valueText` (V5): the text of every typed path passes the check of
-- `d` on `path`. The value is not a literal, and nothing opens the text. The two names are
-- read by one evaluation each.
example (p : PathData) :
    valueOkByName "path".toList "d".toList (valueText PathData.grammar p).toList = true :=
  valueOkByName_valueText (t := .path) (a := .d) (k := .pathData) rfl "path" "d"
    (by decide +kernel) (by decide +kernel) p

-- The same at the kind that the table keys by the element: a typed length on `line`.
example (l : Length) :
    valueOkByName "line".toList "x1".toList (valueText Length.grammar l).toList = true :=
  valueOkByName_valueText (t := .line) (a := .x1) (k := .length) rfl "line" "x1"
    (by decide +kernel) (by decide +kernel) l

-- The same through the walk: a tree that holds the text of any typed path and of any typed
-- transform list is of its grammars. The two equations of the root are evaluations of the
-- name `svg`; the rest is the walk's unfolding and the law at two attributes.
example (p : PathData) (ts : TransformList) :
    valuesOk (svg [el "path" [("d", valueText PathData.grammar p),
      ("transform", valueText TransformList.grammar ts)]]) = true := by
  have hroot : Ns.valuesOk .html "svg" [] = true := by decide +kernel
  have hstep : Ns.step .html "svg" = .svg := by decide +kernel
  have hd : valueOkByName "path".toList "d".toList (valueText PathData.grammar p).toList = true :=
    valueOkByName_valueText (t := .path) (a := .d) (k := .pathData) rfl "path" "d"
      (by decide +kernel) (by decide +kernel) p
  have ht : valueOkByName "path".toList "transform".toList
      (valueText TransformList.grammar ts).toList = true :=
    valueOkByName_valueText (t := .path) (a := .transform) (k := .transformList) rfl "path"
      "transform" (by decide +kernel) (by decide +kernel) ts
  show valuesAt .html (.element "svg" [] [.element "path"
    [("d", valueText PathData.grammar p), ("transform", valueText TransformList.grammar ts)]
    []]) = true
  rw [valuesAt_element, hroot, hstep, valuesAllAt_cons, valuesAllAt_nil, valuesAt_element,
    valuesAllAt_nil, Ns.valuesOk_svg, svgValuesOk_cons, svgValuesOk_cons, svgValuesOk_nil, hd, ht]
  rfl

end WhatwgTest.Html.SvgValues