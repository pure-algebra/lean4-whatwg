# SVG seat to the Effect4 coordinator: what `html/svg` gives the consumer (2026-10-12)

From Claude, seat SVG, at the head of `html/svg` after slice S5. It answers the three guidance
notes and says how lean4-effect4 takes the branch. Rulings R-S17 to R-S19 of `COORDINATION.md`
are the record; this note is a map, and it claims nothing they do not.

**First, what to know.** A picture is now a typed tree. An attribute that has a grammar holds a
typed value, the values of every typed tree pass their grammars by one law, and nothing checks
a value at run time. The branch is not pushed: the owner pushes, and then Effect4 moves its pin.

## 1. The third note, against the record

| Point | Where it landed |
| --- | --- |
| G2 restated: the chapter's rule | `Whatwg/Svg/Value/Greedy.lean`: `Greedy g s o ↔ g.read s = o` (V3b). The bridge to the bare expression is `Deterministic.lean` (V3c). |
| G3: the farthest failure | `Whatwg/Svg/Value/Refusal.lean`: the reader carries its reach; a refusal names the offset (V6). |
| G4: a typed value per attribute | `Whatwg/Html/Node/Svg.lean`: `SvgAttr`, `SvgNode`, `toRaw`, and the connector `SvgNode.valuesOk_toRaw` (V7). `html!` emits typed trees. The reader is `Whatwg/Html/Node/SvgRead.lean` (P4). |
| G5: one table, two laws | `Whatwg/Svg/Value/Attribute.lean`: `ValueKind`, `carrier`, `grammar`, `kindOf`, `AttrValue`. |

One difference from the note. Its table is `Attr.kind? : Attr → Option ValueKind`. The table
here is `kindOf : Tag → Attr → Option ValueKind`, because the sealed text states a value for a
name on some elements only: `x1` on `line`, `x` on `rect` and not on `text`.

## 2. The types Effect4 reads

| Carrier | Kind | Attributes |
| --- | --- | --- |
| `PathData` | `pathData` | `d` |
| `Points` | `points` | `points` |
| `ViewBox` | `viewBox` | `viewBox` |
| `TransformList` | `transformList` | `transform`, `gradientTransform`, `patternTransform` |
| `Length` | `length` | `x1`, `y1`, `x2`, `y2` on `line`; `cx`, `cy` on `circle`, `ellipse`; `x`, `y` on `svg`, `rect`, `image`, `foreignObject` |
| `Extent` | `extent` | `r` on `circle` |
| `AutoExtent` | `autoExtent` | `rx`, `ry` on `ellipse`, `rect`; `width`, `height` on `svg`, `rect`, `image`, `foreignObject` |

A number is `Decimal` (signed) or `Magnitude` (unsigned): an integer mantissa and a power of
ten, never a float. `Decimal.ofInt`, `Decimal.ofScaled v 3` (thousandths) and `Magnitude.ofNat`
are exact, and a numeral is a number: `10 : Decimal`, `320 : Magnitude`, `10 : Length`. Row
354's motion value can hold `TransformList` and `PathData` as its tracks' values.

## 3. How `tools/Tools/View/Output.lean` builds a picture

`WhatwgTest/Html/SvgNode.lean` is this section as code that the build checks. It builds the
shapes `Dev.svg` writes today, from variables.

| `Dev.svg` writes | The typed node |
| --- | --- |
| `<rect x= y= width= height= fill= fill-opacity= data-key=>` | `.element .rect [.attr .x (.user (.ofInt x)), .attr .width (.user (.ofNat w)), .attr .fill c, .data "key" key] []` |
| `<path d="M … C …" fill= stroke=>` | `.attr .d (.path (.moveto false p0 [] [.curveto false (p1, p2, p3) []]))`, a point being `⟨.ofScaled x 3, .ofScaled y 3⟩` |
| `<text x= y= transform="scale(r)" xml:space="preserve">` | `.attr .transform [.scale (.ofInt r) none]`, `.attr .xml_space "preserve"`; `x` and `y` of `text` are text (debt D96) |
| `<clipPath id=><rect …/></clipPath><g clip-path=>` | `.element .clipPath [.attr .id id] […]`, `.element .g [.attr .clip_path ref] children` |
| `<svg xmlns= class= data-look= width= height= viewBox=>` | `.element .svg [.xmlns, .attr .«class» c, .data "look" l, .attr .width (.user (.ofNat W)), .attr .viewBox ⟨0, 0, .ofNat (r * W), .ofNat (r * H)⟩] marks` |

Then, for a tree `n : SvgNode`:

- its values need no check: `SvgNode.valuesOk_toRaw n` holds for every `n`;
- its structure is `Content.validIn ctx n.toRaw`, a Boolean at run time, and
  `Content.explain ctx n.toRaw` gives the path and the reason of a refusal, which replaces
  `problem?` of `tools/Tools/Document/Html.lean`;
- its markup is `Print.render n.toRaw`, and it stands in a document as the raw node `n.toRaw`.

A cut and its end are two device calls today. In a tree the group holds its children, so the
fold over the calls needs a stack. That fold is Effect4's.

## 4. Limits that bear on Effect4

- The printer writes the HTML serialization of the standard. It is what an HTML page holds.
  `tools/Drivers/View.lean` writes each picture to a `.svg` file, which must be XML. The two
  serializations differ in one escape: a no-break space prints as `&nbsp;`, which XML does not
  define. In an SVG subtree the printer escapes every `&` of a text and of a value, so
  `&nbsp;` in its output is that escape and nothing else, and a writer of files may replace it
  with `&#160;`. A writer of standalone files is not in this package: XML is not pinned here.
- A typed literal prints in its grammar's spelling: `M 10 20 L 40 180` prints as
  `M10,20L40,180`. A test that compares markup text will see the new spelling.
- A length takes the ten kinds of the sealed unit table. `rem`, `vw` and `calc()` are refused
  (SV-31). A negative `width` is refused, where SVG treats it as `auto` (SV-35).
- The structure of a large tree that `html!` builds is one kernel evaluation: about 17 seconds
  for 300 `rect` elements (debt D83). A tree that a program builds is checked at run time by
  compiled code and pays nothing of that.
- `text.html` is not sealed, so `x`, `y`, `dx` and `dy` of `text` are text (debt D96). The
  owner granted `geometry.html` alone.

## 5. For the owner

`html/svg` is ahead of `origin` and holds every slice of the plan. Effect4's pin is `2c6e3bc`,
the HTML package before SVG. It moves when `html/svg`, or a `main` that holds it, is on `origin`.

## 6. Placement and limits

- Concept: exact codecs (`exact-codecs`), and the rule that canonical content is first-order
  data.
- Every count and time in this note is from rulings R-S17 and R-S19, measured on this PC by
  the seat or its subagents.
- The seat edits no file outside its worktree. It did elaborate a scratch copy of
  `tools/Tools/Document.lean` and `tools/Tools/Document/Html.lean`, read at `707b9a01`,
  against this branch with `lake env lean`: both elaborate unchanged, so what Effect4 uses of
  the HTML package today is still there. Nothing else of Effect4 was built against it, and
  section 3 is checked by this repository's battery, not by Effect4's code.
