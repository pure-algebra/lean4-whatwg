# SVG seat to the Effect4 coordinator: what `html/svg` gives the consumer (2026-10-12)

From Claude, seat SVG, at the head of `html/svg` after slice S8. It answers the three guidance
notes and says how lean4-effect4 takes the branch. Rulings R-S17 to R-S23 of `COORDINATION.md`
are the record; this note is a map, and it claims nothing they do not. Sections 1 to 6 were
written after slice S5, which the owner pushed. Section 7 says what slice S6 adds. Section 8
is slice S7: a fresh seat ported `tools/Tools/View/Output.lean` to the typed node with this
note as its only guide, and section 3 is rewritten from what it found. Section 9 is slice S8:
the writer of XML, which a `.svg` file needs, and the typed place of a text. Section 10 is
slice S10: the kit a writer of pictures uses, and the first thing to read. Section 11 is
slice S11: exact geometry, for the code that computes edges and outlines.

**First, what to know.** A picture is now a typed tree. An attribute that has a grammar holds a
typed value, and the values of every typed tree pass their grammars by one law. The structure
of a typed tree is one test over its tags, with a law that it is the checker's verdict. So a
picture that a program builds from its numbers can hold both proofs, and check nothing at run
time.

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

`WhatwgTest/Html/SvgPicture.lean` is this section as code that the build checks: a typed writer
for every case of `Dev`, the fold over the calls, and the proof that every picture is valid.
It imports two modules, `Whatwg.Html.Node.SvgValid` and `Whatwg.Html.Print.Render`, and those
load no tactic and no elaborator.

| `Dev.svg` writes | The typed node |
| --- | --- |
| `fill`: `<rect class= x= y= width= height= fill= fill-opacity=>` | `.element .rect [.attr .«class» c, .attr .x (.user (.ofInt b.x0)), .attr .width w, .attr .fill c, .attr .fill_opacity o] []`. The width is `b.x1 - b.x0`, an `Int`: see below |
| `curve`: `<path d="M … C …" fill="none" stroke= stroke-width=>`, whole pixels | `.attr .d (.path (.moveto false p0 [] [.curveto false (p1, p2, p3) []]))`, a point being `⟨.ofInt x, .ofInt y⟩` |
| `shape`: `<path d="M … C … Z M … C … Z" fill-rule="evenodd">`, thousandths | `.attr .d (.path (.ofSubpaths subpaths))`, each subpath its start and its commands, the last `.closepath false`; a point is `⟨(Decimal.ofScaled x 3).trim, (Decimal.ofScaled y 3).trim⟩` |
| `cells`, `text`: `<text x= y= class= font-family= … fill= transform="scale(r)" xml:space="preserve">` | `.attr .transform [.scale (.ofInt r) none]`, `.attr .xml_space "preserve"`, `.attr .font_family f`; `x` and `y` of `text` are lists of lengths, `.attr .x (.single (.user (.ofInt x)))` |
| `cut` … `uncut`: `<clipPath id=><rect …/></clipPath><g clip-path=>` … `</g>` | `.element .clipPath [.attr .id id] […]`, `.element .g [.attr .clip_path ref] children` |
| `hit`: `<rect x= y= width= height= fill="none" pointer-events="all">` | `.attr .fill "none"`, `.attr .pointer_events "all"` |
| the key: `data-key=`, when the key is not empty | `attrs ++ [.data "key" key]` under `if key.isEmpty` |
| `<svg xmlns= class= data-look= width= height= viewBox=>` | `.element .svg [.xmlns, .attr .«class» c, .data "look" l, .attr .width (.user (.ofNat W)), .attr .viewBox ⟨0, 0, .ofNat (r * W), .ofNat (r * H)⟩] marks` |

What a tree forces that a string does not:

- **A size from an integer.** `width` holds an `AutoExtent`, which has no negative value
  (ruling SV-35). `AutoExtent.ofInt? (b.x1 - b.x0)` answers `none` for a negative difference,
  and `.user (.ofNat v.toNat)` writes it as zero. The writer chooses. A numeral is a size:
  `.attr .width 30`.
- **A cut is a group.** `cut` and `uncut` are two calls in a flat list, and in a tree the group
  holds its children. The fold keeps a stack of open cuts. The battery drops an end with no
  open cut and closes a cut with no end, so the tree of every list is balanced.
- **Names.** An attribute is the written name with `_` for `-` and `:`: `fill_rule`,
  `pointer_events`, `xml_space`. The tag type is `Whatwg.Svg.Schema.Tag`, which a helper that
  returns `List (SvgAttr t)` must name. `kindOf .rect .width` says which type a value has.

Then, for a tree `n : SvgNode`:

- its values need no check: `SvgNode.valuesOk_toRaw n` holds for every `n`;
- its structure is `n.okIn ctx`, a test over tags and keys that reads no name, and
  `SvgNode.validIn_toRaw` says it is `Content.validIn ctx n.toRaw` (section 7);
- `Content.explain ctx n.toRaw` gives the path and the reason of a refusal, which replaces
  `problem?` of `tools/Tools/Document/Html.lean`;
- its markup in a page is `Print.render n.toRaw`, and the text of a file that holds it alone
  is `Print.Xml.render n.toRaw` (section 9). It stands in a document as the raw node
  `n.toRaw`, or as `Child.ofSvg n`, a child of the typed HTML tree.

## 4. Limits that bear on Effect4

- `Print.render` writes the HTML serialization of the standard, which is what an HTML page
  holds. `tools/Drivers/View.lean` writes each picture to a `.svg` file, which must be XML:
  that is `Print.Xml.render`, since slice S8 (section 9). The HTML text of a picture is no
  XML where it holds a no-break space, which it writes as `&nbsp;`.
- A typed literal prints in its grammar's spelling: `M 10 20 L 40 180` prints as
  `M10,20L40,180`. A test that compares markup text will see the new spelling. Section 8 lists
  each difference from the text `Dev.svg` writes.
- A length takes the ten kinds of the sealed unit table. `rem`, `vw` and `calc()` are refused
  (SV-31). A negative `width` is refused, where SVG treats it as `auto` (SV-35).
- The structure of a tree that `html!` builds is one kernel evaluation of `okIn`: 0.16 s for
  300 `rect` elements with eight attributes each, where the checker over the written names
  took 8.06 s (ruling R-S20).
- `x`, `y`, `dx` and `dy` of `text` and `tspan` are lists of lengths since slice S8, when the
  owner granted `text.html`: a tree that wrote `.attr .x (toString x)` writes
  `.attr .x (.single (.user (.ofInt x)))`, or `.attr .x 10` for a numeral.

## 5. For the owner

`origin/html/svg` holds the plan through slice S5, and the local branch is ahead of it by slice
S6. Effect4's pin is `2c6e3bc`, the HTML package before SVG. It can move to the pushed head
now, and to S6 once that is pushed.

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

## 7. Slice S6: the structure of a picture, for every input

`Whatwg/Html/Node/SvgValid.lean` holds the test and its law (ruling SV-36, node V8):

- `SvgNode.okAt p n` judges a typed tree at a position by its tags and its keys.
  `SvgNode.okIn ctx n` is the test at an HTML position, where the picture's `svg` stands.
- `SvgNode.validAt_toRaw : validAt p n.toRaw = n.okAt p`. The checker's verdict on the raw
  tree is the test's verdict, at every position. `SvgNode.validIn_of_okIn` is the direction a
  builder uses.

What that gives `tools/Tools/View/Output.lean`:

- **A proof in place of a check.** The test forces no value. `WhatwgTest/Html/SvgValid.lean`
  proves the structure of a box, a curve and a text for every number and string, each by
  `conv => lhs; whnf`, and proves `picture_ok`: the picture is valid for every look, size and
  list of marks, when each mark passes where the marks stand. A `g` keeps that position
  (`below_g`), so a mark that passes among the marks passes inside a clip group.
- **A fast check where a proof is not wanted.** `n.okIn ctx` at run time builds no raw tree and
  writes no name.
- **A typed document.** `Child.ofSvg n` is a `Child ctx` of the typed HTML tree, with the
  test as its premise.

Two more things landed that bear on a consumer:

- A refusal's offset is local (node V6b): a text refused at offset `n`, with a character
  there, shares the refusal with every text that agrees through that character. An error
  shown at the offset is right for whatever follows.
- The path grammar is compared with its sealed chapter by a gate (ruling SV-37):
  `lake exe whatwg_svggrammar` finds the chapter's `svg_path` and the library's description to
  have one language. The gate is unverified code and its verdict is no theorem.

## 8. Slice S7: the port, and what it changed

A seat that had read only this note and the two batteries wrote the typed `Dev.svg` and `svg`,
with the fold, and proved the structure of every picture. The port elaborated on its first
run. Its report is the source of this slice, and its code is now
`WhatwgTest/Html/SvgPicture.lean`.

What the library gained from it:

| The port had to | Now |
| --- | --- |
| prove that a `g` keeps the position, and copy `marks` from a battery | `Pos.inSvg x`, `Pos.belowElement_g`, `SvgNode.okAt_inSvg_g`, at every set of HTML exclusions |
| prove that a forest does not read its order | `SvgNode.okAllAt_eq_all`, `okAllAt_reverse`, `okAllAt_map`, `okAllAt_flatMap` |
| clamp a negative width by hand, with no other route | `Magnitude.ofInt?`, `AutoExtent.ofInt?` |
| write `.user (.ofNat 30)` for a size | `.attr .width 30` |
| match on a command list to put the first moveto in the path | `Path.ofSubpaths` |
| choose between `10.000` and `15e3` for a count in thousandths | `Decimal.trim`: `10`, `13.288`, `15000` |
| print a node through `toRaw` to look at it | `Repr SvgNode` |

`picture_okIn` of the battery holds at every HTML position that admits `svg`, for every look,
size, ratio and list of calls. Each leaf is `cases key.isEmpty <;> conv => lhs; whnf`: the
case split is on the one value that picks the tree's shape. Where a leaf ends in
`false = true`, `Content.explain ctx node.toRaw` on a closed instance names the node and the
reason.

Where the typed printer's text differs from `Dev.svg`'s, on the same calls:

| `Dev.svg` | The typed printer |
| --- | --- |
| one call a line | one line: a line break among the marks is character data, which `svg` does not take |
| `<rect …/>` | `<rect …></rect>` |
| `M 10 20 C 10 30, 30 30, 30 40`, subpaths joined by ` Z M ` | `M10,20C10,30 30,30 30,40`, joined as `ZM` |
| `-0.005`, `0.001` | `-5e-3`, `1e-3`: the shorter spelling |
| `&apos;` for `'`; `&quot;` for `"` in text | `'` as it is; `"` escaped in an attribute and not in text |
| U+00A0 as itself | `&nbsp;` |
| a stray `</g>` or an open `<g>` for an unbalanced list | a balanced tree |

Attribute order and names, classes, `data-key`, `viewBox`, `transform`, clip identifiers and
the escapes of `<`, `>` and `&` are the same.

The comparison is of one sample of nine calls and three edge cases, read by eye against a
copy of `Output.lean`. No theorem relates the two writers.

One thing for Effect4's own gates. The structure theorems reach `Classical.choice`, through
the `String` key of a data attribute and through the checker that a raw subtree is handed to.
`Whatwg.Html` is under this repository's standard ceiling, which admits that axiom. Effect4's
`AGENTS.md`, read at `707b9a01`, says its axiom gate audits the `Effect4.*` and `Test.*`
modules at `propext` and `Quot.sound`. So a theorem such as `picture_okIn` needs nothing in
`tools/Tools/View/`, and in a `Test` battery it would need an exemption by its name.

## 9. Slice S8: a picture as a file

The owner sealed two pins: DOM Parsing and Serialization, which the HTML Standard gives "XML
serialization" to, and the text chapter of SVG 2.

**The writer of XML.** `Whatwg/Html/Print/Xml.lean`:

- `Print.Xml.render : RawNode → String` is the text of a file. For a typed picture `n` it is
  `Print.Xml.render n.toRaw`.
- `Print.Xml.ok` says that the algorithm, run with "require well-formed", throws no exception
  on the tree. `Print.Xml.render?` answers the text of a tree that passes and nothing
  otherwise.

What `ok` asks of a typed picture is small, because the names of the schema pass by one
evaluation of the battery. A key of a `data-` attribute must be a name of XML, so it holds no
space. Each text and each value must hold characters of XML alone, so no control character but
a tab, a line feed and a carriage return. A comment holds no `--`. No node is a named
character reference. These are facts of the strings a program is handed, so `render?` at run
time is the check; the structure and the values are proved, as before.

Its text is nearer to `Dev.svg`'s than the HTML serialization is:

| | `Dev.svg` | `Print.Xml.render` | `Print.render` |
| --- | --- | --- | --- |
| an element with no child | `<rect …/>` | `<rect …/>` | `<rect …></rect>` |
| U+00A0 | itself | itself | `&nbsp;` |
| `>` in a value | `&gt;` | `>` | `&gt;` |
| `"` in a text | `&quot;` | `"` | `"` |
| `'` | `&apos;` | `'` | `'` |
| a tab or a line break in a value | itself | `&#9;`, `&#xA;`, `&#xD;` | itself |
| the namespace | written by hand on the root | on the root, written by the algorithm if the tree does not hold it | none |
| `xlink:href` | no declaration | `xmlns:xlink` declared where none is in scope | none |

A path, a number and the line breaks between calls are as in section 8.
`WhatwgTest/Html/SvgXml.lean` holds the picture of `SvgPicture.lean` as XML, and reads it back
with the reader of this repository's gates, which another hand wrote for the sealed
definitions files.

What the writer does not claim: that it is the algorithm on every tree (the algorithm over a
DOM is not transcribed, and no browser was asked), or a law that a reader of XML reads the
text back. Rulings SV-40 and R-S23 say which debts those are.

XML 1.0 is sealed since slice S9. The two checks of `ok` that come from it, a name and a
character of XML, are `Print.Xml.isName` and `Print.Xml.isChar`, and a gate compares them with
the sealed document at every code point. Nothing a caller writes changes by it.

**The place of a text.** `x`, `y`, `dx` and `dy` of `text` and `tspan` hold a `LengthList`,
`rotate` a `NumberList` and `textLength` an `Extent`. `html!` reads a literal such as
`x="10 20"` by the list's grammar, and prints it as it read it.

**For the module graph.** `Whatwg/Svg/Value/Grammar.lean` holds the definitions and
`Whatwg/Svg/Value/Grammar/Laws.lean` the laws. Nothing in this note's sections changes by it.
## 10. Slice S10: a kit for writing pictures

Everything in sections 3 and 8 still holds. This slice adds the layer above it, so a writer
states what it draws and not how an element is spelt. `WhatwgTest/Html/SvgKit.lean` is
`tools/Tools/View/Output.lean` on the kit, read at `707b9a01`, with `picture_okIn` proved.

**Numbers.** `Decimal` has `+`, `-`, `*`, `<`, `≤`, `min` and `max`, and literals: `(13.25 :
Decimal)`. `Decimal.fixed 3 n` is `n` thousandths. `Decimal.ofQuotient num den places` and
`d.divRound den places` are the two roundings, a half going up. An `Int`, a `Nat` or a
`Decimal` stands where a `Length` is expected, and `AutoExtent.clamp v` writes a negative size
as zero. A sum keeps its places: `0.5 + 0.5` prints `1.0`, and `.trim` makes it `1`.

**Paths.**

```
Pen.begin p0 |>.lineTo p1 |>.curveTo c1 c2 p2 |>.arcTo 5 5 false true p3 |>.close |>.path
Shape.link .bumpY a b          -- d3's vertical link
Shape.bumpY 0.3 a b            -- the same with a reach
Shape.line (.cardinal 0 3) ps  -- a spline, its controls rounded to 3 places
Shape.area .stepAfter top base
```

`Pen.join pens` is one path of several closed parts. Every curve ends at its last point
exactly, and `Pen.current` is the current point of the path chapter.

**Elements and attributes.**

```
Svg.rect b.x0 b.y0 (.clamp (b.x1 - b.x0)) (.clamp (b.y1 - b.y0))
  ([.className "e4-fill", .fill (Rgb.ofNat 0x14110d), .fillOpacity 0.5] ++ SvgAttr.dataKey? key)
Svg.text x y content [.fontFamily "serif", .fontSize 14, .textAnchor .middle]
Svg.clipped "c0" [Svg.rect 0 0 20 10] children
(Svg.Frame.mk W H ratio).svg [.className "e4-view"] marks
```

**A flat list of calls.** `SvgNode.nest wrap calls` makes the forest of marks, starts and ends,
and `SvgNode.okAllAt_nest_of_calls` proves it for every list from one case split on the
writer's own calls and one lemma for the wrapper.

**Text.** `n.render` is the markup for a page. `n.renderXml?` is the text of a file, and
`none` for a tree that is no XML: a control character in a text, or a data key that is no XML
name.

**Changed.** A custom data attribute's key may hold no white space, quotation mark, `/`, `<`,
`=` or `>`: such a key passed before and was written as broken markup.

Where the port's text differs from `Dev.svg`'s is as in section 8, and one more: an edge with
a reach is computed exactly, where `Graph.lean` rounds each control down to a thousandth.

## 11. Slice S11: exact geometry

Sections 3, 8 and 10 still hold, with one change to section 10: a curve is now a list of
segments, and `Shape.bumpY r a b` is `Shape.link (.bumpY r) a b`. This slice is for
`tools/Tools/View/Graph.lean` and `Organic.lean`, which compute edges and outlines as lists of
cubic segments in whole thousandths, with a division rounded down at each step.

**What to know.** The kit's geometry computes in `Rat`, the rational numbers of core. Nothing
is rounded until a number is written into a path, and it is rounded once there, to the nearest
thousandth unless you ask for other places. A count of thousandths enters with `Vec.fixed 3 x y`
and is written back as the same count (`Vec.round_fixed`). A law about a computation is an
equation of values, and `grind` proves the algebra, so the laws you prove by hand on `Int`
are one line each or are in the kit already.

**The same shapes, by name.**

| lean4-effect4 | The kit (`open Whatwg.Svg.Value`) |
| --- | --- |
| `Cubic`, four `Int × Int` | `Cubic`, four `Vec`: the same fields `p0 p1 p2 p3` |
| `Cubic.move dx dy`, `move_move`, `move_zero` | `Cubic.move ⟨dx, dy⟩`, `Cubic.move_move`, `Cubic.move_zero` |
| `Cubic.scale r`, `scale_move` | `Cubic.scale r`, `Cubic.scale_move` |
| `Cubic.size` | `Cubic.taxi` |
| `lerp`, `lerpPt`, a step per mille | `Vec.lerp a b t`, with `t` from `0` to `1` |
| `Cubic.upTo t` | `c.upTo t`; also `c.after t`, `c.split t`, `c.between a b` |
| `Grow.at_ c t` | `c.pointAt t` |
| `Grow.dir c t` | `c.direction t`; `c.velocity t` is the derivative |
| `Grow.normal d` | `Vec.normal d`; of a zero direction it is zero, where yours is `(1000, 0)` |
| `Grow.dist a b` | `Vec.dist a b` |
| `Grow.isqrt n` | `sqrtDown q places`: for a count `n` of `10 ^ -2p`, `isqrt n` is `10 ^ p` times `sqrtDown (n / 100 ^ p) p` |
| `Grow.line a b`, `Graph.straight a b` | `Cubic.line a b` draws the same line with another pace: its point at `t` is `t` of the way along, where yours, `⟨a, a, b, b⟩`, is `3t² - 2t³` of the way. Write `⟨a, a, b, b⟩` to keep your pace; both are written as a lineto |
| `Grow.roundRect x y w h r` | `Cubic.roundRect (Box.ofSize ⟨x, y⟩ w h) r` |
| `Grow.ring` | `Cubic.ring` |
| a quarter arc by `KAPPA` | `Cubic.corner a c b`, the corner `c` between the ends; `Cubic.kappa` is `0.5523` |
| `Grow.segmentThrough p0 p1 p2 p3` | `Curve.cardinalSegment (1 / 6) p0 p1 p2 p3` |
| `Grow.through qs` | `Curve.windows (Curve.cardinalSegment (1 / 6)) (Curve.doubled qs)` |
| `Graph.stepDown L a b` | `(Curve.bumpY r).cubics [a, b]`, and `.linear`, `.stepY` |
| `Rect`, `Rect.Disjoint`, `Rect.holds`, `Rect.move` | `Box`, `Box.Disjoint`, `Box.Contains`, `Box.move` |
| a curve and a shape of `Dev.svg` | `Svg.cubics [c] attrs`, `Svg.loops paths attrs` |

**The laws you need not prove again.**

| Yours | The kit's |
| --- | --- |
| `upTo_move`, `at_move`, `dir_move` | `Cubic.move_upTo`, `Cubic.move_pointAt`, `Cubic.move_direction` |
| `dist_shift` | `Vec.dist_move` |
| `segmentThrough_shift`, `throughFrom_shift`, `through_shift` | `Curve.cardinalSegment_move`, `Curve.windows_map` with `Curve.doubled_map`; `Curve.cubics_move` is the same law for the kit's own curves |
| `line_shift` | `Cubic.move_line` |
| `lerp_shift`, `lerp_end` | `Vec.lerp_add`, `Vec.lerp_one` |
| a moved segment's size, a moved box by its corner | `Cubic.move_taxi`, `Box.ofSize_move` |

**What is new to you.**

- `Cubic.between_pointAt`: the point at `s` of the part from `a` to `b` is the point of the
  whole at `a + s (b - a)`. A reveal of part of an edge is exact.
- `Cubic.contains_pointAt`: the box of a segment's four points holds the segment, so the box
  of an outline is a fold of `Cubic.box`, and `Box.viewBox` writes it rounded outwards.
- `Curve.cubicsClosed`, `cubicsOpen`: d3's closed and open curves.
- `Affine`: a map with an inverse, a quarter turn, an exact rotation (`Affine.turn`), and
  `Affine.fit`, the map of a view box onto a viewport, for a point of the pointer.
- `Curve.chained_cubics` and `Pen.done_cubics`: a curve is a chain, and a chain is written as
  one subpath.

**Where the numbers differ from yours.** You round down at each division, and the kit rounds
once, to the nearest, when it writes. So a control point can differ by a thousandth. Where
your numbers are whole thousandths and no division is in the way, the text is the same.

**The port.** `WhatwgTest/Html/SvgStroke.lean` is `Organic.lean` and the edge code of
`Graph.lean` on the kit, read at `707b9a01`, by a seat that had this section as its only
guide. The definitions are 63 lines for your 114, and the move law with its steps 60 for your
92; nine of your lemmas are the kit's. It proves what you guard: da Vinci's rule for every
count, and that a stroke is a closed outline. What it found:

- `grind` proves the algebra, but give it no opaque application to unfold: generalize a call
  such as `valueNoise seed wave s` first, or it unfolds the hash without end.
- Your spline repeats each end, and the kit's `Curve.cubics` reflects them, so the laws of
  `Curve.cubics` do not reach `through`. The port proves its own (`through_move`,
  `chained_through`, `closed_outline`). A form with repeated ends, and a stroke with a width
  along it, are the next things the kit owes you.
- `Cubic.samples` gives points; a stroke wants a point, a direction and a length run so far.
  The port keeps your `samples` and `runningLengths`.
- A stroke along a straight segment has its knots evenly along it, where yours has them at
  your pace; with noise the knots differ by up to three pixels along the line, and the line
  drawn is the same width.

**Your axiom rule and the kit's numbers.** Your view code is held to `propext` and
`Quot.sound`. In core Lean at this toolchain the definition `Rat.add` reaches
`Classical.choice`, and so do `Rat.mul`, `Rat.div` and every law about them, `Rat.add_comm`
included. So a module under your rule cannot call the kit's geometry, and no way of writing a
proof changes that. Two things follow. A module of yours that computes curves takes the
ordinary three axioms, as this repository's geometry does (ruling R-S25). And what your strict
modules prove about a picture, that a moved call lowers to moved device calls, that a stored
stroke is the stroke, that every key enters, updates or exits, is about structure and needs no
number: the kit will have those laws in a layer of their own, for your own types to be
instances of. A trial of that layer has its cache law with no axiom at all.

**Speed.** Interpreted, your stroke on the kit takes 12.5 ms along eleven segments. A point of a
segment costs about six times what it costs in whole numbers. Rounding the side points to
thousandths before the outline is fitted keeps every number under 32 bits, and the move law
holds through that rounding for every move by whole pixels.

**d3's own tests.** `WhatwgTest/Svg/D3Shape.lean` runs 130 of d3-shape's curve assertions
against the kit. Every number agrees at six places. Two outlines differ, both the area of an
open spline through three points.

`docs/research/2026-10-12-pictures-seams-and-mathlib.md` has each seam between your data and
the kit's, what was tried at it, and the modules that follow, motion as data among them.

## 12. Slices S12 and S13: the seams, and motion as data

You said yes to two things: a module of yours that computes curves takes the ordinary three
axioms, and your expected output may change where a stage rounds once. These two slices build
on that.

**A layer you can use under your own rule.** `Whatwg/Svg/Scene/` has no rational number in
it, and a gate holds every declaration of it to `propext` and `Quot.sound`. What is in it:

| You have | The kit has | What you do |
| --- | --- | --- |
| `Cubic.move`, `Call.move`, `lowerAll_move`, `cachedStroke_eq`, `stroke_from_origin` | `Moves`, `Commutes`, `Commutes.stored`, `Commutes.from_origin` | give an instance `Moves IVec` for your type; the laws are then laws of your type |
| `join`, `join_new`, `join_old` | `join` with twenty laws, for any key with a lawful test | delete yours |
| `Ease`, `tableAt`, `Transition`, `lerp` | `Easing` (`stops`, `cubic`), `Transition`, `mix` | your two tables are `.stops`; `in_`, `out` and `outBack` are `.cubic` |
| `sample`, `sample_end` | `Track`, `Motion`, `Motion.arriveWith`, `Track.at_done`, `Motion.within_atRest` | build tracks from the join; the end law is the kit's |
| a tree drawn by hand | `Tree.spans` with four laws | a node stands over the middle of its leaves |

**A step is one picture and its tracks.** `Whatwg/Html/Node/SvgMotion.lean` writes a motion as
a `style` element of `@keyframes` rules and a `style` attribute on each thing. Your step of
nineteen pictures becomes one picture. `Motion.attrsAt` writes the poses of one moment with no
animation, for your stream and for a reader who asked for less motion.

**What crosses to your whole numbers.** `Whatwg/Svg/Geometry/Grid.lean`: rounding commutes with
a move by a whole count. So `Stroke.commutes_onGrid` is your cache law for a stroke that is
computed in exact numbers and rounded to your thousandths, with no proof about rounding of your
own. Your `lerp` is the exact step rounded down (`mix_eq_floor`).

**The stroke is in the kit.** `Stroke.stroke` with `Stroke.organic`, `Noise`, `Stroke.collar`,
`Stroke.arrowhead` and `Cubic.revealed` are your definitions, moved out of the port, which is
now 443 lines for 851. A filled stroke is revealed through a mask (`Svg.revealed`): the mask's
line is as wide as `Stroke.organic_band` says the stroke can be.

**Two findings about your own code.**

- Your `Transition.at` rounds the progress to a thousandth before the easing. A browser does
  not, and the two differ by up to the slope of the easing over a thousandth: 0.416 against
  0.419 on a spring. The kit reads the easing at the exact share (`Easing.of`).
- Your easing `out` is `1000 - (1000 - p)³ / 10⁶`, which rounds up where the cubic rounds down.
  As CSS draws it, it is `cubic-bezier(1/3, 1, 2/3, 1)`, and the kit's reading is the floor.

**Two pages to look at.** `docs/research/2026-10-12-motion-probe/pfork.html` is one step of
your own frame of `pFork`, read from your rendered picture. `tree.html` is the tree of `pFork`
before and after the body of the fork is written: kept nodes move, kept edges change their
shape and stay joined to them, and new edges and nodes enter level by level. Each page shows
the browser's animation over five still pictures from the kit's own reading.

**What follows.** `docs/research/2026-10-12-pictures-craft-modules.md` ranks sixteen modules.
The first says what holds at every moment of a step: a gap that both pictures have is a gap
of every moment between them, where the things take one timing and the easing stays in range.

## 13. Slice S14: a plan for a step, and what a row keeps

Everything here is under `Whatwg/Svg/Scene/`, inside your axiom rule (`propext` and
`Quot.sound`).

- **`Plan`** replaces `Motion.arriveWith` and `Motion.depart`, which are gone. A plan says what
  a kept thing does, how a new thing enters and how an old one leaves, each as a list of
  changes with their transitions. `Motion.ofJoin key (join key old new) plan` is the step. With
  `plan.Settles` and `plan.Proper`, `Motion.ofJoin_end` is your `sample_end`: at the step's end
  and after, every thing of the new list is at rest. `Join.drawn` is the list your sampler
  builds by hand: the leaving things until the end, then the new list. The port in
  `WhatwgTest/Html/SvgMotion.lean` shows your five-thing step on it.
- **`Row`** is for a rank whose boxes change their widths. `Row.between e s s' ws ws'` moves
  the edges. At every eased progress the row tiles and has the mixed length, and a gap that
  both pictures have is that gap exactly, on a spring that overshoots too. Mixing each width by
  itself loses a pixel of the rank at some moments, and a stagger of kept boxes loses the gap:
  `row.html` shows both with your gap of 16.
- **`Scale`** takes a quantity to a length and names the values that the rounding shows as
  one (`Scale.ties`, `Scale.groups`), for a legend that says "3 and deeper".
- **`Metrics`** and **`Label`**. A face is numbers that a host measures once; your grid of
  cells is `Metrics.mono`, with no host. `Label.fitAll` fits the labels of a picture to their
  rooms and never shows two different labels as one text: where the only cut that fits would
  read as both, each becomes a sign.
- **One finding for you** (`branch.html`). At the exponent two and your default wobble of 350
  per mille a branch is in places wider than its trunk. The proved room for a fork of two is
  171.

Not done: no function of the kit puts the poses of a moment on a thing yet. It is the next
slice, with a step that resumes from where things stand when a new request interrupts it.

## 14. Slice S15, and the answer to guidance 4

Guidance 4 is read and taken (`docs/research/2026-10-12-svg-seat-guidance-4.md`). S14 is the
commit `68e2f23` on `html/svg`: it is the commit for your pin. It is not pushed; the owner
pushes.

What S14 holds for the port, each inside your axiom rule:

- `Plan` closes debt D124. An exit has its own change (`leave`). A kept line can change its
  shape (`kept` gives a list, so `Plan.moving … ++ [(Change.morphOf …, move)]`). A thing that
  stays has no track (`Plan.moving_nil`).
- `Motion.arrive`, `Motion.arriveWith` and `Motion.depart` are gone. `Motion.ofJoin key j plan`
  stands for the three, and `WhatwgTest/Html/SvgMotion.lean` shows your five-thing step on it.

What S15 adds for the port:

- **The reader.** `Motion.frame m key t` is what a thing looks like at a moment: its shift, its
  size, how much of its line is drawn, its opacity. It is your `Seen.under` and your `sample`,
  with the composition that CSS has. `Motion.within_frame_atRest` is your `sample_end` for one
  thing. The port in this repository still has its own reader; it moves onto `Motion.frame`
  next, so port from the next commit's `SvgMotion.lean` if you can wait for it.
- **Your choreography as one function.** `Motion.staged key j plan enterFrom levels rank`. The
  plan's `enter` gives each new thing its share of its level's slot (an edge
  `{ delay := 0, duration := 450 }`, a box `{ delay := 400, duration := 600 }`), and
  `Transition.atMost` carries your caps. For every `enterFrom` of 270 ms or more in a step of
  600 it gives your tracks exactly, by a finite sweep. Laws: no new thing appears before the
  kept things are at rest (`staged_kept_first`), and none before the level above it is done
  (`staged_levels`).
- **One finding** (debt D131). With your defaults the kept things move for 450 of a thousand
  and the first new thing starts at 300. `staged` ends the first stage by `enterFrom`. Either
  number can give way; it is the look's to say.
- **The two checks of a look's read.** `Easing.bounded` is a `Bool` on the easing's data, and
  `Kept.moment` is the law it buys, now also at every rational time
  (`Transition.exact_gap`). `Branch.wobbleRoom n w` is the room of two widths, and
  `Branch.wobbleRoom_apart` the law. A law that states the first check for the kept things of
  a whole step is the seat's next work.
- **The sheet.** Its times are exact now, and a step can be opened at a moment, running or
  paused (`Motion.attrs m key step stem opened paused`). Your C player and a browser then read
  the same share of each duration.

Next, in the order that guidance 4 gives: the definitions that you import reach Lean alone (no
Aesop in their closure); the port on `Motion.frame` and `Motion.staged`; the step-level law for
the first check. Three modules were in hand when the guidance came and land with them: a step
that is interrupted and resumes where each thing is seen, what an edit does to the placement of
a tree, and lanes of states over the steps of a run.
