# Plan: `Whatwg.Css`, CSS adopted as data

Status: **K0 and K1 landed, 2026-10-12** (K1: 178 blocks of eleven modules as 351 rows, no
construct refused; section 7 has what the extractor found). **K3 landed the same day**: the
value definition syntax reads all 186 collected definitions and prints each back, and its
interpreter admits the values the picture kit writes; section 8 has what it found. **K2 landed
after it**: the tokenizer, the writer of tokens and the round trip, with the proof graph
`CSS-PG-SYNTAX` (`docs/CSS-SYNTAX-DAG.md`); section 9 has what it found. **K4 landed on
2026-10-13**, with the first step of K5: the parser, the tree as text, the round trip at a stylesheet,
and the picture kit writing through the one tree; section 10 has what it found. The rest of K5
and K6 are not built. The owner asked for it in these words: "seal the css syntax spec", and "figure a way to
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
  Syntax/   Tree  Tokenize  Serialize  Write            the model of CSS Syntax 3, and the writer
            Parse  Readable  Located  Build             the parser, its premises, a fold, and builders of values
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
| K4 | The tree of rules and the parser; parsing what the writer wrote. Landed, with the kit on the one tree (ruling CS-9) | closes the round trip at rules |
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

## 8. What slice K3 found

- **The reader is not an invertible description of the kit** (`Syn`). That type has no nesting,
  no character outside ASCII, and one character of lookahead; the notation needs all three. The
  reader is a lexer and a parser, with `read (print d) = some d` proved for a well-formed tree.
- **Where the standard leaves a choice**, each docstring quotes the sentence and says the
  reading taken: the scope of a comma that may be omitted, what may take a multiplier, which
  multipliers stack, and that white space is dropped before a value is judged.
- **The kit's scrubbed delay is refused by the grammar as written.** `calc((300 - var(--t, 0)) *
  0.6ms)` is no `<time>` token. That a math function may stand wherever its type would, and that
  a value holding `var()` is judged later, are prose of CSS Values 4 and CSS Variables 1. Slice
  K5 must model both before it can state the writer's soundness for a scrubbed step.
- **Names that only prose defines** need authored readings pinned by digest:
  `<transform-function>` and `<length-percentage>`.
- **One name in two modules**: `scale()`, `<single-animation>`, `animation-duration` and
  `animation-delay` each stand in two levels. A generated data module is per module, and a
  writer names the level it writes for.
- **Debt D97 is not what it was thought to be.** `points` and `viewBox` of SVG 2 are in this
  notation and read. The `transform` attribute is not: CSS Transforms 1 states it in a
  Backus-Naur form of its own, and says that the attribute and the property differ. A guard
  shows the kit's attribute text refused by the property's grammar. Comparing the hand-written
  grammars of `points` and `viewBox` with the sealed lines needs the tokenizer of slice K2.
- **Cost.** The interpreter searches. `animation` with three items takes about 7 ms in the
  evaluator; a refused value of four items of eight parts takes 128 ms. No bound on the search
  is needed at the sizes the kit writes.
- **Open, by name**: that the reader gives only well-formed trees (tested on every line, not
  proved); laws for a juxtaposition with commas and for `{A,B}`, which `cubic-bezier()` and
  `translate()` need in slice K5; the test's corpus is a file written by a script and not yet
  the extractor's tables read by a gate.

## 9. What slice K2 found

- **The round trip holds, and the sealed table of pairs is not enough for it.** Two cases are
  missing from the table: the identifier `--` before the delimiter `>`, and the delimiters `<`
  and `!` before anything that opens with `--`. Each reads back as a token of HTML comments. The
  writer marks both apart from the sealed table (`extraPairs`). The table is a note of the
  standard, so this is no fault of its requirements. Reported on the owner's word, 2026-10-12:
  `https://github.com/w3c/csswg-drafts/issues/14592`.
- **CSSOM's rule for an identifier does not round-trip above U+007F.** It writes such a code
  point as itself, and the tokenizer takes only some of them in a name. The writer escapes the
  others. This is the one place where it leaves the sealed CSSOM text.
- **The premise is a test that computes** (`Writable`): every name the tokenizer can give, with
  its escapes; every string without U+0000; a number whose value a decimal text writes; a unit
  that is a plain identifier and reads as no exponent. Outside it, and written with guards only:
  a URL token, a range of code points, a unit that needs an escape.
- **The standard has no "convert a string to a number" at this pin.** The value of a number is
  read exactly as a rational: its digits, then ten to its exponent.
- **Speed.** 195,000 code points tokenize inside a two-second check under the evaluator.
- **The two missing cases, checked outside the model** (2026-10-12). Upstream's head has the
  same table and tokenizer steps as the pin. Chrome 152 and 155 and Edge 155 write `-->` and
  `[<!--x]` with no comment, by the method of the Web Platform Test for this table
  (`docs/research/2026-10-12-motion-probe/token-pairs.html`). css-tree 3.1.0 writes the same and
  reads its own output back as other tokens. Servo's `cssparser` classes `>`, `<` and `!` as
  needing no separator (read, not run). No report of either case was found upstream; pull
  request 6874 of `w3c/csswg-drafts` fixed the mirror cases in 2021. Two minifiers, lightningcss
  1.33.0 and esbuild 0.27.7, are no evidence either way: they drop a comment between two
  identifiers too.

## 10. What slice K4 found

- **The round trip holds at every level.** The parser reads the tokens of a tree back as the
  tree, from a component value to a stylesheet, and the text of a stylesheet parses to it, on
  one line or one rule a line. No law was left open. The premises are tests that compute
  (`readable`, `writable`, `writableLines`); they suffice and are not necessary.
- **The sealed text drops the last declarations of a block.** `consume a block's contents`
  says "Return rules" at the end of the input and at a right brace, and never appends the
  declarations it holds. By the letter `a { color: red }` has no declaration. The model keeps
  them as the last item. Upstream's head, as fetched on 2026-10-12, has the same text. Not
  reported: that is the owner's to say.
- **The tree needed a fourth kind of rule.** `consume a block's contents` gives rules and lists
  of declarations in order. `Rule.nested` holds a list that stands after a rule. The first list
  of a block is its declarations, for a qualified rule as the standard says and for an at-rule
  by the same reading; nothing is lost, since a list is never empty.
- **What the generic parser does not model**, each named in the header of `Parse.lean`:
  validity in a context (every rule and declaration is kept); the original text of a custom
  property; the `unicode-range` descriptor, which the standard reads again from source text
  that a list of tokens no longer has; parse errors as values.
- **`Writable` was one clause short for text.** A delimiter that is a carriage return is
  writable as a token and is white space after the standard's preprocessing. `writableText`
  asks the clause, and `tokenizeText_serialize` is the law under it.
- **The consumer's stylesheet** (`page.css` at its checkout `6ad8f7b8d`: 11,378 code points,
  2,994 tokens, 80 rules, 247 declarations) is writable, reads back from both texts, and its
  own check, ported onto the tree with `Stylesheet.located`, finds no problem.
- **The kit's text did not move.** With every value built and none spliced, the eight probes
  write the eighteen files of `docs/research/2026-10-12-motion-probe/` byte for byte, and no
  comment stands in any sheet. A coercion from a string to a value was tried and removed: Lean
  coerces each leaf of `a ++ b`, so two halves of a selector were read apart and joined as two
  identifiers. A text becomes a value by name (`Value.ofText`, `Prelude.ofText`).
- **Slice K5, first step.** Judged by the sealed grammars with the interpreter of slice K3:
  256 declarations of steps that are not scrubbed, none refused (`translate`, `scale`,
  `opacity`, `animation` and its longhands, `transform-box`, `transform-origin`, and the
  preludes of `@keyframes` and `@media`). Refused, as section 8 expected: the `animation` of a
  scrubbed step, whose delay is a `calc()` with `var()`. No sealed grammar: `d`,
  `stroke-dasharray`, `stroke-dashoffset`. One theorem: the kit's opacity is admitted for
  every count of thousandths.
- **Open, by name**: that a tree the parser returns passes the premises (false in general:
  `a { b: {} c { } }`); the whole sheet of a step as writable by theorem; math functions and
  `var()` in the interpreter; laws for `{A,B}` and `||`, which `translate`, `scale` and
  `animation` need for a theorem; a `Repr` of the tree; the parser's algorithms in the census.
