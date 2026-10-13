import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.Points

Owner: the value of the `points` attribute of `polyline` and `polygon` (slice S4b of
`docs/SVG-PACKAGE-PLAN.md`, section 5.3). The authority is the definition `DataTypePoints` of
`vendor/w3c-svgwg-47e645ef/master/shapes.html`, `<points> = [ <number>+ ]#`, and the paragraphs
after it.

The typed value is `Points`: one coordinate pair or more. Two statements shape it:

- An odd number of coordinates puts the element in error (the paragraph after
  `DataTypePoints`). So the value holds pairs, and the check refuses an odd count.
- `+` and `#` each ask for one item or more (the reading below). So no value is empty, and the
  check refuses the empty text.

`Points.grammar` is a `Grammar`, so its laws are those of `Whatwg/Svg/Value/Grammar.lean`. The
printer writes one spelling: a comma inside a pair and one space between two pairs,
`750,100 250,900`. The steps under `TermReserialize` of `master/types.html` write a list of
points that way. Each number is spelled as `Decimal` spells it.

The reader takes `wsp* coordinate (comma_wsp? coordinate)* wsp*` with an even count of
coordinates. The names are productions of the path data grammar (`PathDataBNF` of
`master/paths.html`).

## The reading of the notation

The section `syntax` of `master/types.html` says that a Value column is written in the CSS
Value Definition Syntax by default, and its paragraph `attribute-css-value` says that such a
value is parsed against that grammar. The sealed text names the notation and does not restate
its marks. CSS Values defines them, and no CSS Values file is sealed (ruling SV-26). So a
reading below is either a statement of the sealed text, cited, or the mark as the named
notation has it, and each line says which.

- `<number>` is the production `coordinate` of the path data grammar, `sign? number`: the type
  `Decimal` (ruling SV-26).
- `+` is one or more. `#` is one or more, with one comma between two of them. Both are the
  notation's, and the sealed text states neither.
- A comma parts two groups of `#`, and a group carries no value. The sealed text counts
  coordinates and takes them two by two: the paragraph on an odd count, and the mapping to a
  path under `PolylineElement`, which moves to the first coordinate pair and draws a line to
  each one after it. So `1,2 3,4` and `1 2,3 4` are one value.
- White space may stand between two numbers and on either side of a comma. This is the
  notation's. With the comma of `#`, what stands between two numbers is `comma_wsp?`: white
  space in any amount around at most one comma, or nothing.
- Nothing is needed where a sign or a point parts two numbers: `1-2` is a pair. The sealed rule
  is the paragraph after the path data grammar, that a production consumes as much as it can.
  It is applied here because the number is that grammar's.
- White space at either end is read and printed as nothing. This is the notation's. The sealed
  text states it for path data alone: `svg_path` opens and closes with `wsp*`.

What this module does not claim:

- Recovery from an error. The sealed paragraph says that a user agent drops the last, odd
  coordinate and renders the rest. The check refuses the text, and nothing here reads a prefix
  of a text as a value.
- A value for the empty text. The section `syntax` says that a value which fails to parse acts
  as the initial value, here `(none)`: the element is valid and renders nothing. A caller that
  wants the empty list tests for the empty text itself.
- A CSS comment. The note after `attribute-css-value` says that one may stand in such a value.
  The reader takes none.
- That the reader accepts every text of the expression's language. The description is not
  deterministic (`Syn.deterministic` of `Whatwg/Svg/Value/Deterministic.lean`, node V3c of the
  library). `12` is a text of `coordinate coordinate`, and it is one coordinate to the reader.
- That two values which draw one shape are equal. A number is a `Decimal`, so `1.50,2` and
  `1.5,2` are two values.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- The typed value of `<points>`: one coordinate pair or more, in order. -/
structure Points where
  /-- The pair the shape starts at. -/
  head : Point
  /-- The pairs after it. -/
  tail : List Point
  deriving DecidableEq, Repr, Inhabited

namespace Points

/-- The pairs as a list. -/
def toList (p : Points) : List Point := p.head :: p.tail

/-- No value is empty: `+` and `#` each ask for one item or more. -/
theorem toList_ne_nil (p : Points) : p.toList ≠ [] := List.cons_ne_nil p.head p.tail

/-- The description of `<points>`: `wsp*`, a coordinate pair, any number of further pairs each
after `comma_wsp?`, and `wsp*`. A pair prints with a comma, and the next one after one space. -/
def syn : Syn Points :=
  .map (fun p => ⟨p.1, p.2⟩) (fun v => (v.head, v.tail)) (fun _ => rfl)
    (.right wsps (.left (Point.syn.sepBy1 spaceSep) wsps))

/-- Every value prints: a `Points` is made of typed parts. -/
theorem syn_total : syn.Total :=
  Syn.Total.map
    (Syn.Total.right wsps_total
      (Syn.Total.left (Syn.Total.sepBy1 Point.syn_total spaceSep_total) wsps_total))

/-- The grammar of `<points>`. -/
def grammar : Grammar Points := ⟨syn, by decide +kernel, syn_total⟩

end Points

end Whatwg.Svg.Value
