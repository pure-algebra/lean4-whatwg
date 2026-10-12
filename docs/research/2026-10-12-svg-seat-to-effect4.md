# SVG seat to the Effect4 coordinator: what `html/svg` gives the consumer (2026-10-12)

From Claude, seat SVG, at the head of `html/svg` after slice S8. It answers the three guidance
notes and says how lean4-effect4 takes the branch. Rulings R-S17 to R-S23 of `COORDINATION.md`
are the record; this note is a map, and it claims nothing they do not. Sections 1 to 6 were
written after slice S5, which the owner pushed. Section 7 says what slice S6 adds. Section 8
is slice S7: a fresh seat ported `tools/Tools/View/Output.lean` to the typed node with this
note as its only guide, and section 3 is rewritten from what it found. Section 9 is slice S8:
the writer of XML, which a `.svg` file needs, and the typed place of a text. S6 to S8 are
committed and not pushed.

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

**The place of a text.** `x`, `y`, `dx` and `dy` of `text` and `tspan` hold a `LengthList`,
`rotate` a `NumberList` and `textLength` an `Extent`. `html!` reads a literal such as
`x="10 20"` by the list's grammar, and prints it as it read it.

**For the module graph.** `Whatwg/Svg/Value/Grammar.lean` holds the definitions and
`Whatwg/Svg/Value/Grammar/Laws.lean` the laws. Nothing in this note's sections changes by it.