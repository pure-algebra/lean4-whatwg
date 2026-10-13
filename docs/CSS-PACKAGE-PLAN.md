# Plan: `Whatwg.Css`, CSS adopted as data

Status: **K0 and K1 landed, 2026-10-12** (K1: 178 blocks of eleven modules as 351 rows, no
construct refused; section 7 has what the extractor found). K2 and K3 are being
built. The owner asked for it in these words: "seal the css syntax spec", and "figure a way to
mechanize css spec adoption for rigorous foolproof reification". lean4-effect4 asks for the same
thing from its side (entry W5 of `docs/research/2026-10-12-whatwg-requests.md`: a stylesheet
checked by its grammar).

This is the plan for a fifth library of the package, beside `Whatwg.Html` and `Whatwg.Svg`. It
follows the development order of `AGENTS.md` and the method the package already has for a
standard as data (`docs/HTML-PACKAGE-PLAN.md` ruling HP-7, `docs/SVG-PACKAGE-PLAN.md` rulings
SV-2, SV-25, SV-37 and SV-42, `docs/DESIGN-BASIS.md` DB-01). Facts were read at `html/svg`
`c33ce29`.

## 0. Why CSS, and why now

The picture kit writes CSS: the style sheet of a motion, the `animation` of each thing, the
`style` of a frame (`Whatwg/Html/Node/SvgMotion.lean`). Until now that text was "written by rule
and read back by nothing" (debt D119). Three grammars of SVG values are also stated by their
standard in the notation of CSS value definitions, and no gate reads those lines (debt D97).
Every keyword set that a seat typed from memory is a debt of the same kind.

CSS is a better subject for adoption as data than HTML was. Its specifications are Bikeshed
sources, and they carry four kinds of block that are data already:

| Block | What it states | Where (at the pin) |
| --- | --- | --- |
| `<pre class='propdef'>` | a property: name, value grammar, initial value, what it applies to, whether it inherits, its animation type | 9 in CSS Animations 1, 7 in CSS Transforms 2 |
| `<pre class='descdef'>` | a descriptor of an at-rule or a media feature | 38 in Media Queries 5 |
| `class=prod` | a production, in the value definition syntax | 12 in CSS Values 4, 13 in CSS Color 4 (and one more inside a comment, which is passed over) |
| `<pre class='railroad'>` | a diagram of a token or a rule, in a small notation of its own | 28 in CSS Syntax 3 |

And CSS Syntax 3 gives its tokenizer and parser as algorithms, in `<div algorithm>` blocks that
the census gate already reads (profile `Bikeshed`, ruling R-P1 of `SPEC-MANIFEST.md`).

## 1. The method: five instruments, written once

Adopting a CSS module must be mechanical. The work that needs judgment is done once, in five
instruments. After that a module is adopted in three steps: seal it, add its record to the list
of modules, regenerate.

```text
seal        vendor/w3c-csswg-drafts-<pin>/<module>/Overview.bs          the bytes, by digest
extract     lake exe whatwg_cssblocks                                   blocks to rows, by rule
read        Whatwg/Css/Values/Definition.lean                           one reader of the value definition syntax
model       Whatwg/Css/Syntax/{Token,Tokenize,Parse,Serialize}.lean     the algorithms of CSS Syntax 3
tie         theorems, and gates with controls                           what the rows and the model are worth
```

1. **Seal.** One commit of `w3c/csswg-drafts` is pinned (`50337328`, ruling R-S15). A module is
   its `Overview.bs`, stored whole, with its blob hash and digest in `docs/PROVENANCE.md`.
2. **Extract.** One gate, `whatwg_cssblocks`, reads every sealed module and writes one table for
   each kind of block under `generated/css/`, each row with the byte span and the digest of its
   block. It interprets nothing: a row holds the block's own text, field by field. It refuses a
   field or a construct it does not know, as `whatwg_svgdefinitions` does, so a block is never
   half read.
3. **Read.** The value definition syntax is one grammar: keywords, types in angle brackets,
   the combinators (juxtaposition, `&&`, `||`, `|`, brackets) and the multipliers (`*`, `+`,
   `?`, `{A,B}`, `#`, `!`). CSS Values 4 defines it. `Whatwg.Css.Values.Definition` is its tree
   and its one reader and printer, written as an invertible description of the kit
   (`Whatwg/Svg/Value/Grammar.lean`, ruling SV-25). The gate reads every extracted production
   and every `Value:` line through it and writes them as Lean values in generated modules. A
   line the reader does not read fails the gate. No grammar of a property is typed by hand.
4. **Model.** The tokenizer and the parser of CSS Syntax 3 are Lean functions, one for each
   algorithm of the standard, each naming its census row. The input is a list of code points,
   which is what the standard's preprocessing gives.
5. **Tie.** What the rows and the model are worth is said by theorems where a theorem can be
   had, and by a gate with controls where the standard's side is text.

## 2. What is proved, and against what

- **The round trip, which is the standard's own requirement.** CSS Syntax 3, section
  "Serialization": "The only requirement for serialization is that it must round-trip with
  parsing". The same section gives a table of the pairs of tokens that need a comment between
  them. The writer of `Whatwg.Css` serializes by that table, read from the sealed bytes, and the
  theorem is: the tokens of what it writes are the tokens it was given, up to runs of white
  space. Lifted to rules: parsing what the writer wrote gives the tree it wrote. This turns
  debt D119 from "read back by nothing" into a theorem about the standard's own tokenizer.
- **A writer is sound against the sealed grammar of what it writes.** One interpreter gives
  every value definition its meaning over component values. For each property the kit writes,
  the theorem is: for every input, the value written is admitted by the grammar that the
  property's `propdef` states. The grammar is a generated value, so the theorem cannot drift
  from the standard without the gate failing first.
- **The diagrams are a second opinion, not an authority.** CSS Syntax 3 says its railroad
  diagrams are informative and incomplete. The gate reads each as a regular expression and
  compares it with the language of the token it draws, by the walk over derivatives that
  `whatwg_svggrammar` uses (ruling SV-37), with controls that must differ. A named class of a
  diagram ("a-z A-Z _ or non-ASCII") is an authored reading, pinned to the diagram's digest.
- **Facts about properties are rows, not memory.** "The kit animates only properties whose
  animation type is by computed value" is a check of the kit's list of properties against the
  `Animation type` field of sealed rows.

What is not claimed, ever: that a browser implements the standard. A browser is a host profile.
Chrome 152's readings of the constructs the kit writes are host observations
(`docs/research/2026-10-12-motion-probe/css-facts.html`), and Web Platform Tests of
`css/css-syntax` are the host corpus once they are sealed (slice K6).

## 3. Target shape

```text
vendor/w3c-csswg-drafts-50337328/   css-syntax-3 sealed; the modules of section 5 as they are sealed
WhatwgGates/CssBlocks.lean          the extractor; CssBlocksEmit.lean, its tables, drift check and controls (whatwgbin/, lakefile, CI as the other gates)
generated/css/                      <module>-properties.tsv, -descriptors.tsv, -productions.tsv, -diagrams.tsv, -tables.tsv, and INDEX.tsv
Whatwg/Css/
  Syntax/   Token  Tokenize  Tree  Parse  Serialize     the model of CSS Syntax 3, and the writer
  Values/   Definition  Admits                          the value definition syntax as data, and its interpreter
  Data/     <Module>                                    generated: the productions and properties of a module
WhatwgTest/Css/                     the kit's writer as the test; controls
```

`Whatwg.Css` is under the ordinary axiom ceiling (ruling R-11), not on the strict list: it reads
`String` and `Char`, and core's lemmas about them reach `Classical.choice`.

The tree that `Whatwg/Html/Node/Css.lean` gives the picture kit (a declaration, a qualified
rule, an at-rule) is the parser's own tree. There is one carrier, written and read.

## 4. Rulings

| Id | Ruling |
| --- | --- |
| CS-1 | The library is `Whatwg.Css`. The authority is the sealed Bikeshed source of each module at the one pinned commit of `w3c/csswg-drafts`. Ruling SV-26 stored one file of that commit; it now stores a module whenever a slice adopts it, and each is named in `docs/PROVENANCE.md`. |
| CS-2 | No grammar, property or keyword of CSS is typed by hand. A block of a sealed source becomes a row by the extractor, and a row becomes a Lean value by the reader of the value definition syntax. What is written by hand is the reader of each notation, the model of each algorithm, and a reading of prose pinned to the digest of what it reads. |
| CS-3 | The extractor interprets nothing and refuses what it does not know (rulings HP-13 and SV-2). It is unverified code with controls; its PASS is a procedure's verdict (ruling SV-37). |
| CS-4 | The value definition syntax has one tree, one reader and one printer, from one description. A sealed line that the reader does not read fails the gate. |
| CS-5 | A value definition has its meaning from one interpreter over component values. A writer's soundness is a theorem against the generated value of the property it writes. |
| CS-6 | The tokenizer and the parser are modelled one function for each algorithm of CSS Syntax 3. CSS Syntax 3 joins the census as a standard of the Bikeshed profile, so its coverage is reported as the other standards' is (`docs/SPEC-COVERAGE.md`). |
| CS-7 | The first theorem of the library is the round trip of the standard's section "Serialization", with the table of pairs read from the sealed bytes. |
| CS-8 | A railroad diagram is informative. It is compared with the model and never overrides it. A disagreement is a finding to record, with its witness. |
| CS-9 | One tree is written and read. The picture kit's CSS types are that tree. |
| CS-10 | A claim names its tier: a theorem; a gate's verdict; a host observation under a named profile. |

## 5. Pins

All at the one pinned commit of `w3c/csswg-drafts`, `50337328`, each `<module>/Overview.bs`,
fetched into an empty directory, compared with its upstream blob hash and size, and then copied
(ruling R-S32 of `COORDINATION.md`; the digests are in `docs/PROVENANCE.md`). `css-transforms-1`
has been there since slice S4c.

| Module | Why | Blob | Bytes |
| --- | --- | --- | --- |
| `css-syntax-3` | tokens, the tokenizer, the parser, the round trip of serialization | `e84f922f` | 150,058 |
| `css-values-4` | defines the value definition syntax, numbers, lengths, times, `calc()` | `8c0e7713` | 231,897 |
| `css-animations-1` | `animation` and its longhands, `@keyframes` | `d240f804` | 54,937 |
| `css-animations-2` | `animation-composition`, `animation-timeline` | `703d31d1` | 45,969 |
| `css-easing-2` | `linear()`, `cubic-bezier()`, `steps()` | `6dae1b21` | 36,116 |
| `css-transforms-2` | `translate`, `scale`, `rotate` as properties | `eae60396` | 79,384 |
| `mediaqueries-5` | `prefers-reduced-motion` | `374b3914` | 166,185 |
| `cssom-1` | how an identifier and a string are serialized | `ba405696` | 155,470 |
| `css-color-4` | a colour (ruling SV-26 had none sealed) | `128e6261` | 469,216 |
| `css-variables-1` | custom properties and `var()`, which lean4-effect4's page rules use | `604ae631` | 37,179 |

Not sealed, and named where a module leans on memory for it: SVG 2's chapters on painting and
paint servers (the keyword sets of `Whatwg/Html/Node/SvgKeyword.lean`), WAI-ARIA (the two ARIA
references of `Whatwg/Html/Content/Document.lean`), CSS Properties and Values API (`@property`).
## 6. Slices

| Slice | What | Lands with |
| --- | --- | --- |
| K0 | The pin of CSS Syntax 3, this plan | `docs/PROVENANCE.md`, `SPEC-MANIFEST.md` |
| K1 | `whatwg_cssblocks`: the four kinds of block and the data tables, for every sealed module | `generated/css/`, the gate's row in `AGENTS.md` and CI |
| K2 | Tokens, the tokenizer, the serializer, the round trip for the tokens a writer makes; CSS Syntax 3 in the census | proof graph `CSS-PG-SYNTAX` in the ledger |
| K3 | The value definition syntax: tree, reader, printer, interpreter; the generated data modules | pays debt D97 for the SVG value grammars stated in this notation |
| K4 | The tree of rules and the parser; parsing what the writer wrote | closes the round trip at rules |
| K5 | The picture kit's writer on the tree, sound against `animation`, `translate`, `scale`, `opacity`, `@keyframes`, `linear()`, `cubic-bezier()`, `@media` | pays debt D119; answers entry W5 |
| K6 | Web Platform Tests of `css/css-syntax` sealed and run as the host corpus | a host profile |

Open questions, each for the slice named: a round trip for every token list, not only a
writer's (K2 states the premise it needs and leaves the general law as an open edge); whether
the interpreter of `||` and `&&` is decidable at the sizes the properties use without a search
bound (K3); escapes in identifiers that the kit's stems could need (K2, with `cssom-1`).

## 7. What slice K1 found in the sources

- **A fifth and a sixth kind of block.** Besides the four kinds of section 0 and the data
  tables, two `pre` elements with no class hold productions that slice K5 needs: the grammar of
  `@keyframes` in CSS Animations 1, and the whole grammar of a media query in Media Queries 5.
  The extractor reads a `pre` with no attribute where one of its lines opens with a `dfn` and
  `=`; such rows have the kind `pre`.
- **A block inside a comment** (CSS Color 4) is passed over and counted, so that a block class
  that the scanner did not read cannot go unseen.
- **Not resolved, for slice K3's reader**: a footnote mark inside a production of CSS Syntax 3
  (`'+'?† n`, five times); four expressions of CSS Values 4 whose name stands outside their
  block; four diagrams of Media Queries 5 with no name.
- **The texts of `Animation type`**, for slice K5: `by computed value` and its variants 8 times,
  `discrete` 4, `not animatable` 14, and one each of `as SLERP` and `transform list`.
- **For ruling CS-8**: the diagram of `wsp` in CSS Transforms 1 has a form feed where its prose
  has a line feed. The diagram is informative; the module `Whatwg/Svg/Value/Transform.lean`
  follows the prose.
