import Whatwg.Html
import WhatwgTest.Html.Svg

/-!
# WhatwgTest.Html.SvgValues

Readers, controls and finite evaluations of the judgment of SVG attribute values (slices S4b
to S4d and S5 of `docs/SVG-PACKAGE-PLAN.md`; rulings SV-30 and SV-34):
`Whatwg/Html/Content/Values.lean`, and the typed tree that `html!` builds
(`Whatwg/Html/Syntax/Elaborator.lean`, `Whatwg/Html/Node/Svg.lean`).

The judgment is beside the checker, not inside it. A control here shows each side of that
line: a tree that `validIn` admits and `valuesOk` refuses, and a tree for the reverse. A
refusal names the offset in the value at which no reading continues, and one line shows that
the offset is the furthest character a reading reached.

A tree that `html!` builds needs no evaluation of the judgment. Its term is the raw tree of a
typed tree, so the connector `SvgNode.valuesOk_toRaw` gives its values, for a literal and for
a spliced value alike. The elaborator reads a literal by its grammar to make the typed value,
and refuses a literal that the grammar refuses, at the attribute's token.

What this battery does not claim: that the value `html!` reads from a literal is the one its
author meant, or that the print of a value is the literal it was read from. The reader takes
many spellings, and the printer writes one.
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

-- An attribute with no kind takes any text. That is a limit of the package: a paint is not
-- judged. `x` on `text` is text too: there it is a list, and the chapter that states it is not
-- sealed.
#guard valuesOk (svg [el "rect" [("fill", "no colour"), ("class", "")], el "text" [("x", "ten")]])

-- Control of the table's key: on `rect` the name `x` is a length of the sealed chapter
-- `geometry.html`, and the same text is refused.
#guard !valuesOk (svg [el "rect" [("x", "ten")]])

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

-- The message of a refusal.
#guard (Reason.attribute "d" (.valueAt 12)).describe ==
  "the value of the attribute `d` is not of its kind: no reading continues after 12 characters"

/-! ## `html!` builds a typed tree -/

/-- An icon with a value of each grammar, as markup. Its path has about 250 characters, and the
kernel takes seconds to open a `String` of that length (ruling SV-30). The elaborator reads each
literal by its grammar, and the term holds the values read: constructors and numbers. -/
def icon : Child Ctx.flow :=
  html! <svg viewBox="0 0 24 24"><path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 \
    10-10S17.52 2 12 2zm0 3c1.66 0 3 1.34 3 3s-1.34 3-3 3-3-1.34-3-3 1.34-3 3-3zm0 14.2c-2.5 \
    0-4.71-1.28-6-3.22.03-1.99 4-3.08 6-3.08 1.99 0 5.97 1.09 6 3.08-1.29 1.94-3.5 3.22-6 \
    3.22z" /><g transform="translate(1,2) rotate(45)"><polygon points="0,0 1,0 1,1" /></g></svg>

-- Reader of the connector (V7) at the tree `html!` builds: the term is the raw tree of a typed
-- tree, so its values pass by the law. Nothing is evaluated, and the kernel opens no text.
example : valuesOk icon.raw = true := SvgNode.valuesOk_toRaw _

-- The same as the absence of a refusal.
example : explainValues icon.raw = none := SvgNode.explainValues_toRaw _

-- The structure is the term's own proof: the law of structure at one evaluation of `okIn`,
-- which reads tags and keys.
example : validIn Ctx.flow icon.raw = true := icon.valid

/-- A stroke, in spellings that an author writes: white space, and a comma or none. -/
def stroke : Child Ctx.flow :=
  html! <svg viewBox=" 0,0  320 200 " width="320"><path d="M 10 20 L 40 180" transform="translate( 1 2 )" /></svg>

-- The printed markup spells each typed value as its grammar prints it, in one spelling.
#guard Print.render stroke.raw ==
  "<svg viewBox=\"0 0 320 200\" width=\"320\"><path d=\"M10,20L40,180\" " ++
  "transform=\"translate(1,2)\"></path></svg>"

/-- A spliced value is a term of the attribute's type: path data at `d`. -/
def traced (d : PathData) : Child Ctx.flow := html! <svg><path d={d} /></svg>

-- Reader of the connector at a spliced value: the law holds for every `d`, with no premise.
example (d : PathData) : valuesOk (traced d).raw = true := SvgNode.valuesOk_toRaw _

-- The spliced value prints by its grammar.
#guard (traced (.path (.moveto false ⟨.ofInt 1, .ofInt 2⟩ [] [.closepath true]))).raw ==
  svg [el "path" [("d", "M1,2z")]]

-- Control: a `String` is no value of `d`. Before slice S5 a spliced `String` built a tree that
-- the judgment could refuse; now the term does not elaborate.
/--
error: Type mismatch
  d
has type
  String
but is expected to have type
  PathData
-/
#guard_msgs (error) in
example (d : String) : Child Ctx.flow := html! <svg><path d={d} /></svg>

/-! ## `html!` refuses a literal that its grammar refuses -/

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

-- The geometry properties: a length on `rect`, and a size that must not be negative.
/-- error: the value of the attribute `x` is not of its kind: no reading continues after 0 characters -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><rect x="ten" /></svg>

/-- error: the value of the attribute `width` is not of its kind: no reading continues after 0 characters -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><rect width="-3" /></svg>

-- An `svg` below an HTML element below an integration point is a part of a raw literal. The
-- elaborator reports the located refusal of the judgment there, at the same token.
/-- error: the value of the attribute `d` is not of its kind: no reading continues after 0 characters -/
#guard_msgs (error) in
example : Child Ctx.flow :=
  html! <svg><foreignObject><div><svg><path d="L 1 1" /></svg></div></foreignObject></svg>

/-! ## A typed value needs no evaluation -/

-- Reader of `SvgAttr.valueOk_toPair`: the written pair of every typed path passes the check of
-- `d` on `path`. The value is a variable, and nothing opens its text.
example (p : PathData) :
    valueOkByName "path".toList "d".toList (valueText PathData.grammar p).toList = true :=
  SvgAttr.valueOk_toPair (t := .path) (.attr .d p)

-- The same at the kind that the table keys by the element: a typed length on `line`.
example (l : Length) :
    valueOkByName "line".toList "x1".toList (valueText Length.grammar l).toList = true :=
  SvgAttr.valueOk_toPair (t := .line) (.attr .x1 l)

end WhatwgTest.Html.SvgValues