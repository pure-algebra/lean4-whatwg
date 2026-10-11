# Plan: `Whatwg.Svg`, inline SVG beside `Whatwg.Html`

Status: **S0, S1 and S2 executed, 2026-10-11** (the ledger is §8). Slices S3 and S4 are designed
here and not built. The owner adopted the seat's review on 2026-10-11. §3.1 holds its model, §4
its rulings, and §7 the owner's decisions.

This is the plan for inline SVG in the `whatwg` package. An HTML tree holds an SVG figure as
checked, first-order data. The assignment is `docs/research/2026-10-11-svg-seat-brief.md`. The
plan has the shape of `docs/HTML-PACKAGE-PLAN.md`. Its order is ruling R-S1 of `COORDINATION.md`:
design first, then land in slices. Facts were read at `html/svg` `e74dc0d`.

Three words are used in one meaning each:

- The **seam** is the set of rules by which an HTML tree holds SVG content.
- An **integration point** is an SVG element whose children are HTML content again.
- A **dangling name** is a name that a definition cites and no sealed definition declares.

## 0. What the consumer needs

lean4-effect4 builds a document as a `Whatwg.Html.RawNode` tree. `Whatwg.Html.Content.validIn`
checks the tree, and `Whatwg.Html.Print.renderDoc` writes it. Its module is
`tools/Tools/Document/Html.lean`, read at its commit `707b9a01`. Its pictures are SVG, written as
strings by `tools/Tools/View/Output.lean`. No content model checks those strings, and no reader
reads them.

| Need | What answers it | Slice |
| --- | --- | --- |
| `svg` inside a paragraph, a figure or a table cell | `svg` is a foreign tag of the HTML schema, admitted where its categories stand | S3 |
| `svg`, `g`, `defs`, `rect`, `path`, `text`, `clipPath` | the schema, generated from the sealed definitions | S2, S3 |
| `class`, `style` and custom properties | the core attributes; CSS stays text | S3 |
| `data-key` on every mark, `data-look` on the root | `data-*` on every SVG element | S3 |
| `@keyframes` in a `style` element | the element's text, escaped when printed | S3 |
| `title`, `desc`, `role` and `aria-*` | the descriptive elements and the `aria` category | S3 |
| `d`, `viewBox`, `transform`, `points`, numbers, lengths | typed values with a printer, a checker and a reader | S4 |
| a refusal that names its node | a located refusal in the library | S3 |

The sealed definitions declare every element and attribute that `Output.lean` writes today,
apart from `xmlns` and `data-*`. This is a reading of the two sources. The battery of S3 makes
it a test.

The consumer writes its own refusal walk, `problem?`, in `tools/Tools/Document/Html.lean`. The
library gives `validIn` as a Boolean and no refusal. S3 moves that walk into the library.

## 1. Authority order

1. **The HTML Standard** at its pin (`vendor/whatwg-html-746f2ede/source`) owns the seam. It
   says where `svg` stands, where the namespace changes and how a foreign element is written.
2. **SVG 2** at `w3c/svgwg` commit `47e645ef` owns the SVG elements. It owns their categories,
   content models, attributes and value grammars.
3. **The definitions files** of that commit are the draft's machine-readable index. The chapter
   files are the same authority in prose. Where the two disagree, the projection records a row.
   No one repairs a sealed file or a projection.
4. **CSS Transforms 1** owns the `transform` value, which SVG 2 cites. It is not pinned yet:
   S4c seals it (SV-26). No other CSS specification is an authority of this package.
5. **Browsers and validators** give host observations under a named profile. They repair no
   statement.

The pinned draft is the Editor's Draft. Its `master/publish.xml` names the Candidate
Recommendation of 2026-06-04 as the published version. The published document has no
machine-readable definitions, so the pin is the repository commit.

## 2. The pin

`vendor/w3c-svgwg-47e645ef/` holds thirteen files of `w3c/svgwg` at commit
`47e645ef7cb61490e6975ddbcfa1997c9e972cc3` (2026-10-07). `docs/PROVENANCE.md` records the fetch
and the cross-check. `generated/vendor-manifest.tsv` holds each digest.

| File | Bytes | What the plan reads in it |
| --- | --- | --- |
| `master/definitions.xml` | 83,931 | 30 elements, 13 element categories, 8 attribute categories, 10 attributes |
| `master/definitions-filters.xml` | 20,896 | 26 filter elements |
| `master/definitions-masking.xml` | 3,090 | `mask` and `clipPath` |
| `master/definitions-compositing.xml` | 2,303 | terms only |
| `specs/animations/master/definitions.xml` | 7,488 | 5 animation elements and the category `animation` |
| `master/publish.xml` | 3,273 | the list of the five definitions files of SVG 2 |
| `master/struct.html` | 153,803 | the `data-*` rule and the ARIA role table |
| `master/paths.html` | 52,259 | the path data grammar |
| `master/shapes.html` | 37,360 | the `points` value |
| `master/coords.html` | 149,848 | the `viewBox` value; `transform` by reference to CSS |
| `master/types.html` | 140,699 | the attribute syntax notation |
| `LICENSE.md`, `README.md` | 152 and 999 | the licence pointer |

**The brief asked for `master/definitions*.xml`.** The pin holds nine more files, for three
reasons:

- `master/publish.xml` lists the definitions files of SVG 2. It names a fifth file, under
  `specs/animations/`. That file declares the category `animation`, which 20 content models cite.
- The definitions hold no value grammar. The grammars of S4 are in four chapter files.
- The `data-*` rule and the ARIA roles are in `master/struct.html` alone.

### 2.1 What the definitions hold

`lake exe whatwg_svgdefinitions` prints these counts, and the projections under `generated/`
hold the rows. The evidence word is "reproduced": the gate recomputes them from the sealed
bytes at every run.

| Kind | Count | Note |
| --- | --- | --- |
| `element` | 63 | 32 names hold an upper-case letter |
| `elementcategory` | 17 | each lists its member elements |
| `attributecategory` | 17 | 16 categories: `presentation` is declared twice, in two files |
| `attribute`, outside an element or a category | 14 | three list elements that do not cite them |
| `property` | 117 | the presentation attributes are a list of these names |
| attribute names in the schema | 321 | a name may take different values on different elements |

Each element states its content model by one of five kinds:

| Kind | Elements | Meaning in the definitions |
| --- | --- | --- |
| `anyof` | 50 | any number of the listed elements and of the listed categories' members |
| `any` | 4 | any elements or character data: `desc`, `title`, `metadata`, `foreignObject` |
| `text` | 2 | character data: `style`, `script` |
| `textoranyof` | 3 | character data and the listed elements: `text`, `tspan`, `textPath` |
| prose | 4 | a sentence: `a`, `feDiffuseLighting`, `feSpecularLighting`, `animateMotion` |

So the definitions hold what S2 and S3 need: element names, categories, content models and
attributes.

### 2.2 What the definitions get wrong or leave out

The gate finds ten dangling names, and `generated/svg-dangling.tsv` lists each with its citers:

| Dangling name | Cited as | Cited by |
| --- | --- | --- |
| `altGlyphDef`, `color-profile`, `font`, `font-face` | element | `mask` |
| `document element event` | attribute category | 34 elements |
| `style` | attribute category | 20 elements |
| `externalResourcesRequired` | attribute | `clipPath`, `filter`, `feImage` |
| `transform` | attribute | `clipPath` |
| `color-profile`, `kerning` | property | the second `presentation` entry |

`transform` dangles only as a cited attribute. The first `presentation` entry lists it as a
presentation attribute, so `clipPath` has it through that category.

Five things are in no definitions file:

- every value grammar (§5.3);
- the `data-*` attributes, which `master/struct.html` gives to every SVG element;
- the roles an element may take, also in `master/struct.html`;
- the `transform` value, which `master/coords.html` leaves to CSS Transforms;
- the CSS number, which the attribute syntax of `master/types.html` leaves to CSS.

### 2.3 Licence

`LICENSE.md` places every document of the repository under the W3C Document License. The 2023
version permits a derived work in software and in its documentation. Such a work carries a
notice: it names W3C as the copyright holder and names the source by title and address. Each
generated file of S2 carries that notice.

## 3. Target shape

```text
vendor/w3c-svgwg-47e645ef/           the sealed SVG 2 sources (S1)
WhatwgGates/Xml.lean                 a total reader of the XML subset the sealed files use (S2)
WhatwgGates/SvgDefinitions.lean      the rows, the four projections, the drift check (S2)
WhatwgGates/SvgDefinitionsEmit.lean  the schema's resolution and the modules' emitter (S2, S3a)
WhatwgGates/EmitLean.lean            the Lean spelling that the HTML and SVG emitters share (S2)
whatwgbin/SvgDefinitions.lean        the entry point of `whatwg_svgdefinitions` (S2)
generated/svg-*.tsv                  the projection: elements, categories, attributes, dangling names (S2)
Whatwg/Svg.lean                      root of the library `WhatwgSvg`
Whatwg/Svg/
  Data/      Universe  Mask  NameTable                    a finite universe, a set as a mask, a name table (S3a)
  Schema/    Tags  Categories  Attributes  ContentModel   generated (S2; masks since S3a)
  Schema/    Readings                                     authored, digest-pinned (S2)
  Schema/    Universe                                     authored: the instances and the tables' laws (S3a)
  Content/   Context                                      the SVG position, its transition, one node's judgments (S3a)
  Value/     Grammar  Decimal  PathData  Points  ViewBox  Transform    (S4)
Whatwg/Html/Schema/Foreign.lean      generated: the parser's tables for foreign content (S3b)
Whatwg/Html/Node/Walk.lean           the walk and its two laws (S3b)
Whatwg/Html/Svg.lean                 the seam: `Ns`, `Pos`, the integration points (S3b)
Whatwg/Html/Content/Valid.lean       the Boolean algebra and `validIn` (S3b)
Whatwg/Html/Content/Explain.lean     the refusal algebra and `explain` (S3c)
Whatwg/Html/Print/Render.lean        the print state, the decoder, the round trip (S3d)
WhatwgTest/Svg/, WhatwgTest/Html/Svg*.lean   batteries
```

The diagram shows the data's route. It claims nothing: §6 lists each claim with its evidence.

```mermaid
flowchart LR
  V[sealed definitions] -->|read by| G[whatwg_svgdefinitions]
  G -->|writes| P[generated/svg-*.tsv]
  G -->|writes| S[Whatwg.Svg.Schema]
  S -->|read by| A[Whatwg.Svg.Content: the SVG position]
  A -->|one summand of| Q[Pos: the seam's position]
  H[HTML Standard: categories, parser tables] -->|read by| Q
  Q -->|state of| W[the walk]
  T[RawNode tree] -->|folded by| W
  W -->|Boolean algebra| C[validIn]
  W -->|refusal algebra| E[explain]
  W -->|print algebra| R[renderDoc]
  X[Whatwg.Svg.Value] -->|prints an attribute value into| T
```

**Dependency direction.** `Whatwg.Svg` imports no module of `Whatwg.Html`. The seam imports
`Whatwg.Svg`. A consumer imports `Whatwg.Html.Content.Valid` and `Whatwg.Html.Print.Render`, as
it does today.

### 3.1 The model

The owner adopted the review `docs/research/2026-10-11-svg-seat-review.md` on 2026-10-11
(ruling R-S6 of `COORDINATION.md`). Its points T1 to T9 are the model of this package, and its
points M1 to M8 are the rules of the meta level. The packet
`docs/research/2026-10-11-svg-theory/README.md` cites each source from its page. This section
states each point as the plan builds it. Where the review left a choice, the seat's choice is
marked **Seat**.

**T1. Validation is one top-down pass.** A `RawNode` is an unranked ordered tree. The checker
reads it once, from the root:

- a state is a position: what may stand there;
- the transition takes a position and an element's name to the position of its children;
- acceptance at a node is a local test of the position, the name, the attributes and the
  children's names.

A child's position is a function of its parent's position and its own name. So the grammar is
single-type, in the sense of Murata, Lee, Mani and Kawaguchi, and one top-down pass validates
it without backtracking. The seam of HTML and SVG is a new grammar of that kind. It is
single-type because `Pos.child` is a function, and no closure theorem gives it. The reachable
positions are finite, and the plan claims no bound on their number.

**T2. The namespace is a component of the state.** The seam's position is a sum:

```lean
inductive Pos where
  | html (c : Whatwg.Html.Content.Ctx)
  | svg (c : Whatwg.Svg.Content.Ctx) (excl : Whatwg.Html.Schema.Exclusions)
```

The HTML Standard's tree construction has its own automaton on namespaces. The seam writes it
once, from the sealed `source`:

```lean
inductive Ns where | html | svg
def Ns.step : Ns → String → Ns
theorem Pos.child_ns (p : Pos) (name : String) : (p.child name).ns = p.ns.step name
```

The checker's state is `Pos` and the printer's state holds `Ns`. Both factor through `Ns.step`,
so they cannot disagree about a node's namespace.

**Seat.** `Pos.svg` carries the HTML exclusions (SV-9). An integration point hands them back to
the HTML position below it. `Ns` has two values: `math` is refused (SV-10), so no valid tree
reaches MathML.

**T3. An SVG content model is a set of tags with a text bit.** The kinds of the definitions
spell points of that Boolean algebra:

- `anyof` is the union of the listed elements and of each listed category's members;
- `any` is every element of the schema, with the text bit;
- `text` is the text bit alone;
- `textoranyof` is `anyof` with the text bit.

The generator computes the resolution, and the library holds its value. A dangling name
resolves to the empty set (SV-3).

The SVG `a` element is transparent. Its sealed sentence reads: "Descriptive content, plus any
element or text allowed by its parent's content model, except for another a element. If the
parent is a switch element, use the content model of the nearest ancestor that isn't a switch."
So the SVG grammar is not local, and the position holds two models:

```lean
/-- What may stand at a position: the admitted elements, and whether character data may. -/
structure Content where
  tags : Mask Tag
  text : Bool

/-- A position in an SVG subtree. `model` is what the children of the position's element may
be. `outer` is the model in force at the nearest ancestor-or-self that is not a `switch`. -/
structure Ctx where
  model : Content
  outer : Content
```

**Seat.** Two components suffice. Let an `a` stand at a position. If its parent is not a
`switch`, the parent's model is `outer`. If its parent is a `switch`, the model of the nearest
ancestor that is not a `switch` is `outer` again. So `a` inherits `outer` in both cases.

**Seat.** "Except for another a element" removes `a` from the model of that `a`. It is not a
descendant exclusion: the sentence speaks of the content model, and the model of a `g` inside
the `a` lists `a`. So `<a><g><a>` is admitted and `<a><a>` is refused. The SVG position carries
no exclusion set of its own.

Two readings count. `feDiffuseLighting` and `feSpecularLighting` take exactly one light source,
and `animateMotion` takes at most one `mpath`, in any order. So a model also holds count
intervals, each over a set of tags. Its test reads only the multiset of the children's tags.

The HTML exclusions only grow along a path, and the admission of a tag is antitone in them. Both laws are
stated over `Pos`, for both namespaces.

**T4. A finite set over a generated universe is a mask over that universe.** Every finite set of the schema is a
subset of a generated enumeration. It is a `Nat` whose bit `i` is the value of index `i`:

```lean
/-- A finite universe: `all` lists every value at its index. -/
class Universe (α : Type) where
  all : List α
  index : α → Nat
  all_index : ∀ a, all[index a]? = some a

structure Mask (α : Type) where
  bits : Nat

def Mask.mem [Universe α] (m : Mask α) (a : α) : Bool := m.bits.testBit (Universe.index a)
```

Union is `|||`, intersection is `&&&`, and each law of membership is a core lemma
(`Nat.testBit_or`, `Nat.testBit_and`, `Nat.testBit_xor`). The kernel evaluates `|||`, `&&&`
and the shifts natively on literals, and `Nat.testBit` unfolds to a shift and an `&&&`. So one
definition is the specification and the fast test, and a tactic reads a mask back as one
literal. `Nat` has no complement. A difference is written with `^^^`, and the top of a universe is
`ofList all`. No law needs two masks with the same members to be equal. The index is Lean's own `ctorIdx`. The seat measured at the
toolchain `v4.33.1` that these lemmas and an instance by `cases a <;> rfl` stay under the
strict ceiling.

**T5. One walk, several algebras.** The checker, the located refusal and the printer are folds
over `RawNode` with one inherited attribute. The walk is written once. An algebra also sees the
raw children, because a sequence test reads their names:

```lean
/-- A top-down walk: a state, its transition, and what each node makes of its children. -/
structure Walk (S R : Type) where
  step : S → String → S
  element : S → String → List (String × String) → List RawNode → List R → R
  leaf : S → RawNode → R

def Walk.run (w : Walk S R) (s : S) : RawNode → R       -- mutual with `runAll`, structural
def Walk.runAll (w : Walk S R) (s : S) : List RawNode → List R
```

Two laws are proved once, by induction on `RawNode`:

- **W1, fusion.** If `h` commutes with the node maps of `A` and `B`, and their transitions are
  equal, then `h (A.run s n) = B.run s n`.
- **W2, state homomorphism.** If `f : S → S'` commutes with the transitions, and the node maps
  factor through `f`, then `A.run s n = B.run (f s) n`.

`explain_none_iff` is W1 at `Option.isNone`. The namespace agreement of T2 is the hypothesis of
W2 at `Pos.ns`.

**T6. A name table is an exact embedding.** A table is a writer `chars : α → List Char` and a
reader. The reader is built generically:

```lean
/-- A name table: each value's spelling, and a guess of the value that a spelling names. -/
structure NameTable (α : Type) where
  chars : α → List Char
  guess : List Char → Option α

/-- The value that a spelling names: the guess, kept only if it spells the input. -/
def NameTable.read (n : NameTable α) (s : List Char) : Option α
theorem NameTable.read_exact : n.read s = some a → n.chars a = s
theorem NameTable.read_chars (h : ∀ a, n.guess (n.chars a) = some a) (a : α) :
    n.read (n.chars a) = some a
```

**Seat.** The generated decision tree is the guess, and `read` checks its answer. So the
exactness holds by construction, for any guess, and it is proved once for every table. The
retraction needs one premise per table. One `decide` over the census discharges it. No proof
splits over a generated match. This is rule M1 at object level: the generated code proposes, and
a checked function decides.

Case restoration is an exact embedding modulo a normaliser. For every schema name `n`, the
parser's table sends the lower-case form of `n` back to `n`.

**T7. The printer is an exact embedding on well-formed trees.** The HTML package proves
`decode_render` and `render_injective_of_wf`. S3 keeps that strength. `wf` and the decoder take
the print state. In SVG no element is void and no text is raw. `decode_render` is proved for
trees that hold SVG.

**T8. Every value grammar of S4 is regular.** Path data, `points`, `viewBox`, the number and
the `transform` list nest no production. So S4 is one library and a transcription per grammar
(§5.3).

**T9. The schema projection is a function of sealed bytes.** The drift gate is its evidence.
A list attribute is split on commas and trimmed, because a category name holds a space. The
reader normalises an attribute value as XML 1.0 section 3.3.3 says.

### 3.2 What the theory packet corrects

The research partner read each source that the review cites. Its packet is
`docs/research/2026-10-11-svg-theory/README.md`. It contradicts or weakens the review at these
points, and the plan reads each one as the sources state it:

| Point | What the sources say | What the plan does |
| --- | --- | --- |
| T1, the name | The checker is no "top-down deterministic hedge automaton" of the cited texts. It is a single-type grammar, validated in one top-down pass. | §3.1 uses that name. |
| T1, composition | The cited closure is under intersection. A sum of states is no closure result. | The seam is built by hand, and its law T2 is proved here. |
| T1, enumeration | The states are finite, with an exponential bound once exclusions are in the state. | No proof enumerates the reachable positions. |
| T3 | Only the test at one node is the paper's count expression. The paper's schema is local, and this model is not. | The plan says "count intervals" and cites the paper for the node's test alone. |
| T4 | `Nat.testBit` is no kernel primitive, and `Nat` has no complement. | §3.1, T4, says what unfolds and what is native. |
| T5 | The cited theorem is for ranked parse trees. "Paramorphism" carries no law. | W1 and W2 are the seat's proofs, in `Whatwg/Html/Node/Walk.lean`. W1 has the premise of equal transitions. |
| T8 | No cited paper proves the retraction for free. Each proved round trip has an unambiguity premise. The retraction needs the reader to be complete on the printer's image. | `Syn.ok` is that premise (§5.3). A description is an inductive value, so it erases to its expression. |
| T8, the lexer | Verbatim's lexer recurses on an accessibility proof. | The reader recurses on the description and on fuel. |
| M4 | The kernel does unfold a definition by well-founded recursion. | The rule stands: recurse structurally. Its reason is the cost of the accessibility proof, which nobody here measured. |

The packet's two facts about the toolchain agree with what the seat measured. The index
function is `ctorIdx`, and Lean generates it for every inductive type.

## 4. Rulings

The owner ruled on 2026-10-11 (ruling R-S6 of `COORDINATION.md`). SV-8, SV-20 and SV-26 are the
owner's rulings. SV-22 to SV-25 are the review's, which the owner adopted. The rest are the
seat's proposals of S1, changed where §3.1 changes them.

| Id | Question | Ruling |
| --- | --- | --- |
| SV-1 | authority | The order of §1. The HTML Standard owns the seam, and SVG 2 at `47e645ef` owns the elements. |
| SV-2 | schema source | The schema is generated from the five definitions files that the sealed `master/publish.xml` lists. No row is typed by hand. |
| SV-3 | dangling names | A dangling name is a row of `generated/svg-dangling.tsv`. A dangling element is admitted nowhere, and a dangling category is empty. The gate fails when the set of rows changes. |
| SV-4 | prose content models | Each of the four is an authored reading in `Whatwg/Svg/Schema/Readings.lean`, pinned to the digest of the entry it reads. The reading of `a` is transparency with `switch` skipped (T3). It is not a fixed set. |
| SV-5 | the tree | `RawNode` is unchanged. A node's namespace is an inherited attribute of its path. The walk carries it down. |
| SV-6 | layering | The library `WhatwgSvg` owns `Whatwg/Svg/` and imports nothing of `Whatwg.Html`. The walk and the seam are in `Whatwg.Html`. |
| SV-7 | where `svg` stands | The HTML Standard's category lists name `SVG svg` and `MathML math` under flow, phrasing, embedded and palpable content. The HTML gate reads those items. The HTML `Tag` gains two foreign tags, which have no markup name, as `pcdata` has none. Admission of `svg` is the existing `admitsWith`, exclusions included. No hand table says where `svg` stands. |
| SV-8 | integration points | The children of `foreignObject` are checked as flow content, and those of `title` as phrasing content. The HTML Standard says both. The children of `desc` are checked as phrasing content too (owner ruling). A later ruling may widen this, and none narrows it. |
| SV-9 | exclusions | The exclusions of the HTML context pass through an SVG subtree. `<a><svg><foreignObject><a>` is refused. |
| SV-10 | MathML | `math` is refused with the reason "MathML is not modelled". No library is planned. |
| SV-11 | names | A tree holds each name as the serializer writes it. The checker compares names exactly, so `viewbox` is not `viewBox`. |
| SV-12 | `xmlns` | `xmlns` is admitted on an SVG element only with the SVG namespace as its value. `xmlns:xlink` is admitted only with the XLink namespace. The rule is the HTML Standard's, so it is in the seam. |
| SV-13 | values before S4 | S3 admits an attribute by its name. Its value is unchecked text until S4 gives its grammar. |
| SV-14 | CSS | The `style` attribute, the `style` element's text and each presentation attribute's value are text. CSS is a foreign boundary. |
| SV-15 | roles | `role` takes any text in S3. The graphics roles belong to a specification that is not pinned. |
| SV-16 | located refusal | The library gives one refusal with a path and a reason. It is complete against `validIn`: the refusal is absent exactly when `validIn` is true. |
| SV-17 | the printer | In an SVG subtree no element is void and no text is raw. The printer returns to the HTML rules below an integration point. |
| SV-18 | numbers | A number is an exact decimal. No value of the library is a float. |
| SV-19 | reader and checker | For each value grammar, the checker is the domain of the reader. The reader accepts every spelling the grammar admits, and the printer writes one. |
| SV-20 | ceiling | `Whatwg.Svg` is a strict prefix from its first module (owner ruling). A function that must traverse a `String` is an exact exception with its reason. None exists: a lookup reads a `List Char`, and the seam converts. |
| SV-21 | licence notice | Each generated file names its source and W3C's copyright (§2.3). |
| SV-22 | finite sets | Every finite set of the schema is a mask over its universe (T4). |
| SV-23 | traversals | The checker, the refusal and the printer are algebras of one walk (T5). |
| SV-24 | name tables | A name table is an exact embedding built generically (T6). |
| SV-25 | value grammars | A value grammar is a regular expression as data. One invertible description reads and prints it (T8). |
| SV-26 | the CSS pin | `w3c/csswg-drafts` is pinned at one commit, and only the CSS Transforms 1 source is sealed. A number is SVG's own `number` production. No CSS Values file is pinned. A length takes only what the sealed SVG text states (owner ruling). |
| SV-27 | unknown names | An element whose name is in neither schema is refused at every position. This holds under `metadata` too, whose model is `any`: the checker knows no rule for the subtree. |

## 5. Slices

| Slice | Work | Exit |
| --- | --- | --- |
| S0 | merge `origin/html-h7` into `html/svg` | done: ruling R-S2 of `COORDINATION.md` |
| S1 | this plan; the pin, sealed and cross-checked | done: ruling R-S3 |
| S2 | the projection gate and the generated schema | done: ruling R-S4 |
| S3a | the universe, the mask and the name table; the schema as masks; the SVG position | the laws U1, B1, N1 and K1 of §6 are proved; the gate passes in both modes |
| S3b | the walk and its two laws; the foreign tags and the parser's tables; `Pos`; the Boolean algebra | W1, W2, T2, X1, X2, N2, N3, C1 and C2 are proved; every HTML battery passes unchanged |
| S3c | the refusal algebra | C3 and C4 are proved; a refused tree's path is the bad node's |
| S3d | the print state, the decoder, the round trip | P1, P2 and P3 are proved for trees that hold SVG |
| S3e | the `admits` tactic and `html!` | the tactic renders the refusal of `explain`; `html!` builds an SVG figure |
| S4a | the grammar library and its generic laws | V1 and V3a are proved over the description |
| S4b | the number, path data, `points` and `viewBox` | each grammar's premise holds; the battery replays the chapter's own examples |
| S4c | `transform`, after the CSS pin | the pin is sealed; the grammar's premise holds |

Each part lands as commits by explicit paths, with its narrow build, `lake build`, the axiom
receipt and the gates it reaches. No part runs the trust self-test (ruling R-S5).

### 5.1 S2: the schema as data

The gate is `lake exe whatwg_svgdefinitions`, in the shape of `whatwg_htmlstandard`. It does five
things:

1. It refuses a sealed file whose digest is not the pinned one.
2. It reads `master/publish.xml` and takes the definitions files from it.
3. It reads each file with a total XML reader. The reader refuses a construct it does not know,
   with the byte offset.
4. It writes or checks four projections and the schema modules.
5. It fails on one byte of drift, and it names the first differing line.

The XML reader covers what the five files use: elements, attributes in either quote, comments,
character data and the five named character references. It has no `partial` function. Fuel
bounds each loop.

| Output | One row per | Columns |
| --- | --- | --- |
| `generated/svg-elements.tsv` | element | file, name, anchor, kind, categories, elements, attribute categories, geometry properties, attributes, own attributes, span digest |
| `generated/svg-categories.tsv` | element or attribute category | kind, file, name, members |
| `generated/svg-attributes.tsv` | attribute declaration | owner kind, owner, name, animatable, anchor |
| `generated/svg-dangling.tsv` | dangling name | name, cited as, cited by |

| Module | Holds |
| --- | --- |
| `Whatwg.Svg.Schema.Tags` | `Tag`, `Tag.all`, `Tag.name`, `Tag.chars`, and `Tag.guess` as a character decision tree |
| `Whatwg.Svg.Schema.Categories` | `Category` and each one's members, as a mask |
| `Whatwg.Svg.Schema.Attributes` | `Attr` with its names and its guess, `AttrCategory` with its members, and each tag's attributes as a mask |
| `Whatwg.Svg.Schema.ContentModel` | `Tag.model`: the categories and elements as stated, the resolved set and the text bit, and what a read sentence adds |

As built, S2 differs from its design in three ways:

- No module repeats the raw rows in Lean. The four projections are the raw rows, and nothing in
  Lean reads them a second time.
- An attribute reaches an element in two directions. An element cites an attribute, or an
  attribute outside every element lists the element. Three attributes list elements that do not
  cite them, so a tag's own attributes are the union.
- The ledger carries `Whatwg.Svg` as an unrouted prefix (debt D78), not as a leaf record. A leaf
  record holds receipts, and S2 states no law. The graph of S3 fences these modules.

S2 emitted each set as a list. S3a emits it as a mask (SV-22), and the projections keep every
byte.

### 5.2 S3: the seam

**S3a. The data of `Whatwg.Svg`.** Three modules of `Whatwg/Svg/Data/` hold the declarations
of T4 and T6 with their laws. They name no schema. The debt H-C2 of §6.1 moves them to a home
that the HTML schema can import.

The generator emits masks, a writer `chars` and a guess per name table. One authored module,
`Whatwg/Svg/Schema/Universe.lean`, holds the four `Universe` instances, the two name tables and
their retractions. `Whatwg/Svg/Content/Context.lean` holds the position of T3:

```lean
def Ctx.outside : Ctx                              -- where an outermost `svg` stands
def Ctx.child (c : Ctx) (t : Tag) : Ctx            -- the model of `t`; `outer` kept under `switch`
def Ctx.admits (c : Ctx) (t : Tag) : Bool := c.model.tags.mem t
def boundsOk (t : Tag) (children : List Tag) : Bool   -- each interval of `t` holds its count
def attrOk (t : Tag) (name : List Char) : Bool        -- the tag's attributes, or `data-*`
```

`Ctx.child` reads three generated facts of `t`: its own content, whether it inherits, and what
it removes. One generated set, `handsOn`, names the elements under which `outer` is kept. At
this pin it holds `switch` alone. The gate refuses two readings that name different sets.

**S3b. The walk and the seam.** `Whatwg/Html/Node/Walk.lean` holds `Walk`, `run`, `runAll`, W1
and W2. It imports `Whatwg.Html.Node.Raw` alone.

The HTML gate reads two more things from the sealed `source`:

- the foreign items of the four category lists, which become the tags `svg` and `math`;
- the parser's tables for foreign content, which become `Whatwg/Html/Schema/Foreign.lean`. They
  are the start tags that end foreign content, the SVG names that the parser restores, and the
  SVG integration points.

The seam, `Whatwg/Html/Svg.lean`, holds `Ns`, `Ns.step`, `Pos`, `Pos.child`, `Pos.ns` and the
law `Pos.child_ns`. `Pos.child` is total:

| Position | Name | Position of the children |
| --- | --- | --- |
| `html c` | an HTML element `t` | `html (c.child t)` |
| `html c` | `svg` | `svg (Ctx.outside.child .svg) c.excl` |
| `html c` | any other | `html` at the base `nothing`: nothing is admitted |
| `svg c x` | `foreignObject` | `html` at flow content, with the exclusions `x` |
| `svg c x` | `desc`, `title` | `html` at phrasing content, with the exclusions `x` |
| `svg c x` | another SVG element `t` | `svg (c.child t) x` |
| `svg c x` | any other | `svg` at the empty model |

The Boolean algebra is `check : Walk Pos Bool` in `Whatwg/Html/Content/Valid.lean`. Its test at
an HTML element is the conjunction that `validIn` holds today. Its test at an SVG element is
the admission of the tag, the attributes and the bounds. A child's tag in a sequence is its HTML tag, or
its foreign tag: `<figure><svg/><figcaption/><svg/></figure>` is refused by the sequence of
`figure`.

`validIn c n` becomes `check.run (.html c) n`. The seat measures
`WhatwgTest/Html/DecideBenchmark.lean` and `WhatwgTest/Html/MarkupBenchmark.lean` before and
after. If either build slows by more than a tenth, `validIn` stays a mutual function with the
SVG cases, and one connector, `validIn_eq_run`, ties the two. Either way two equations bound
the change:

- At a name the HTML schema knows, `validIn` equals the conjunction it equals today. The
  existing `validIn_element` keeps its statement.
- At a name that is neither an HTML element nor `svg`, `validIn` is false.

**S3c. The located refusal.** `Whatwg/Html/Content/Explain.lean` holds the second algebra:

```lean
inductive Reason where            -- no element of the position's namespace; not modelled; not
  | …                             -- admitted here; an attribute; a repeated attribute; the
                                  -- sequence; a count; character data; a comment
structure Refusal where
  path : List Nat                 -- child indices from the root
  reason : Reason

def explainWalk : Walk Pos (Option Refusal)
def explain (c : Ctx) (n : RawNode) : Option Refusal := explainWalk.run (.html c) n
theorem explain_none_iff (c : Ctx) (n : RawNode) : explain c n = none ↔ validIn c n = true
```

One lemma per namespace says that a node's reason is absent exactly when its Boolean test
holds. `explain_none_iff` is then W1. It needs no second induction. The three prose functions
of today retire: `attrProblem?`, `valueProblem?` and the consumer's own `problem?` (M2).

**S3d. The printer.** The print state is the namespace and one bit:

```lean
structure PrintState where
  ns : Ns
  raw : Bool                       -- the parent is an HTML raw-text element

def printWalk : Walk PrintState (List Char)
def renderIn (s : PrintState) (n : RawNode) : List Char := printWalk.run s n
def renderChars (n : RawNode) : List Char := renderIn ⟨.html, false⟩ n
```

In the SVG namespace every element prints a start tag, its children and an end tag. Text is
escaped, under a `style` or a `script` too. `wf` and the decoder take the state. `decode_render`
and the two injectivity laws are proved again, for every tree that `wf` accepts at the root
state. The existing battery `WhatwgTest/Html/Print.lean` passes unchanged.

**S3e. The meta level.** The `admits` tactic renders the refusal of `explain`, so its message
is complete by C3. It reads a mask as one literal and writes no second reader of a context (M3).
`html!` keeps each SVG name exactly, and takes a string literal for a name that is no identifier
(`xml:space`). It declares no token that the trust gate refuses.

**The battery.** Each line is a reader, a control or a finite evaluation:

| Case | Kind | Expected |
| --- | --- | --- |
| `<p><svg>` | finite evaluation | admitted |
| `<svg><div>` | control | refused: `div` is not an SVG element |
| `<svg><foreignObject><div>` | finite evaluation | admitted |
| `<a><svg><foreignObject><a>` | control | refused by the inherited exclusion |
| `<svg><title><div>` | control | refused: `title` holds phrasing content |
| `<svg><a><a>` | control | refused: `a` removes `a` |
| `<svg><a><g><a>` | finite evaluation | admitted: the removal is not a descendant exclusion |
| `<svg><switch><a><rect>` | finite evaluation | admitted: `a` inherits the model of `svg` through `switch` |
| `<feDiffuseLighting>` with two light sources | control | refused by the count |
| `<figure><svg/><figcaption/><svg/>` | control | refused by the sequence of `figure` |
| `<math>` | control | refused: MathML is not modelled |
| `<svg><metadata><x>` | control | refused: `x` is in no schema |
| `<svg><style>a<b</style>` | finite evaluation | printed with `&lt;` |
| `<svg><rect>` with no child | finite evaluation | printed `<rect></rect>`, never void |
| `viewBox` and `xml:space` | finite evaluation | printed as written |
| the consumer's picture, built as a tree | finite evaluation | `validIn` is true, and the tree prints |
| `explain_none_iff` at a refused tree | reader | the refusal's path is the bad node's |
| `decode_render` at a tree with SVG | reader | the decoder returns the tree |

### 5.3 S4: the values

**S4a. The library.** One module, `Whatwg/Svg/Value/Grammar.lean`, holds three layers:

```lean
/-- A set of ASCII characters, as a mask over the code point. -/
structure CharSet where
  bits : Nat

/-- A regular expression over character sets: what a description erases to. -/
inductive Regex where
  | empty | eps | set (s : CharSet) | seq (a b : Regex) | alt (a b : Regex) | star (a : Regex)

inductive Regex.Matches : Regex → List Char → Prop        -- the language
def Regex.accepts : Regex → List Char → Bool              -- by derivatives
theorem Regex.accepts_iff : r.accepts s = true ↔ r.Matches s

/-- A typed description of a regular grammar. It reads a value and prints one. -/
inductive Syn : Type → Type 1
def Syn.erase : Syn α → Regex
def Syn.print : Syn α → α → Option (List Char)            -- one spelling, or none outside the image
def Syn.read : Syn α → List Char → Option (α × List Char) -- the longest match; no backtracking
def Syn.ok : Syn α → Bool                                 -- one character decides each choice
```

Two laws are proved once, over the description:

- **V1, the retraction.** If `g.ok` holds and `g.print v = some s`, then `g.read` on `s`,
  followed by a text that cannot continue the match, returns `v` and that text.
- **V3a, the soundness of the reader against the expression.** If `g.read s = some (v, rest)`, then `s` is `pre ++
  rest`, and `g.erase` matches `pre`.

`g.ok` is the premise of V1. It is a decidable test of the description: at each sequence, each
choice and each repetition, the next character decides. One `decide` discharges it per grammar.

**Seat.** The size of this layer is a risk. V1 over `Syn` may not be proved within S4a. The seat
then lands the regular expression, its matcher and V3a, and proves V1 per grammar in S4b. The
claims of §6 then say so.

**S4b and S4c. The grammars.** Each grammar is one small module: the typed value, the
description, the proof of `ok`, and three corollaries.

```lean
def print : α → List Char
def read : List Char → Option α
def check (s : List Char) : Bool := (read s).isSome
theorem read_print (v : α) : read (print v) = some v
theorem check_print (v : α) : check (print v) = true
```

| Grammar | Source at the pin | Typed value |
| --- | --- | --- |
| number | the `number` production of the path data grammar | `Decimal` |
| path data, `d` | the grammar under `PathDataBNF` in `master/paths.html` | a list of commands, each with its arguments |
| `points` | `DataTypePoints` in `master/shapes.html` | a list of pairs |
| `viewBox` | `ViewBoxAttribute` in `master/coords.html` | four numbers |
| `transform` | CSS Transforms 1, pinned at S4c (SV-26) | a list of transform functions |
| length | what the sealed SVG text states (SV-26) | a number and a unit |

**The number** is an exact decimal: an integer mantissa and a power of ten. Its normal form has
no trailing zero in the mantissa. The invariant is a predicate, and one function normalises. A
conversion from a rational with rounding is a widening, not an embedding. The consumer's layout
numbers cross it, so the module states its bound.

**What the reader is.** The path data grammar admits many spellings of one value: `M 100-200`
and `M100,-200`. So `read` is not exact. It is exact modulo the normaliser `print ∘ read`, which
holds by `read_print`. The plan claims the retraction and V3a, and no more.

The module's `String` face is one function per grammar, in the seam. Every law is stated over
`List Char`.

## 6. Anticipated proof graph

S2 is passive data and states no law. S3 is an admission, so it opens a proof graph,
`SVG-PG-SEAM`, with its ten edges in the ledger, and that graph fences the schema modules. Each
grammar of S4 is an exact representation and closes with a leaf record of its laws.

Two consumers read these nodes. **D** is lean4-effect4's document builder,
`tools/Tools/Document/Html.lean`. **P** is its picture writer, `tools/Tools/View/Output.lean`.

| Node | Statement | Kind | Planned evidence | Slice | Consumer |
| --- | --- | --- | --- | --- | --- |
| G1 | the projections and the schema modules equal a regeneration from the sealed bytes | drift gate | reproduced | S2 | P |
| U1 | a Boolean predicate that holds on `Universe.all` holds at every value | reflection, once per class | proved | S3a | D, P |
| B1 | `mem` sends union, intersection, difference and `ofList` to the Boolean operations | homomorphism | proved | S3a | P |
| N1 | `read s = some a → chars a = s`, and `read (chars a) = some a`, for every name table | exact embedding | proved: generic, with one `decide` per table | S3a | P |
| K1 | the resolved set of each model is the join of its stated categories and elements | finite check | proved by `decide` | S3a | P |
| N2 | the parser's tables restore every schema name from its lower-case form | exact embedding modulo a normaliser | proved by `decide` | S3b | P |
| N3 | no SVG element name is a start tag that ends foreign content | finite check | proved by `decide` | S3b | P |
| W1 | fusion of two algebras of the walk | law of the walk | proved | S3b | D |
| W2 | a state homomorphism carries one algebra's run to another's | law of the walk | proved | S3b | D |
| T2 | `(p.child name).ns = p.ns.step name` | homomorphism of automata | proved | S3b | D, P |
| X1 | the HTML exclusions only grow along `Pos.child` | monotonicity, both namespaces | proved | S3b | D |
| X2 | the admission of a tag at a position is antitone in its exclusions | antitonicity, both namespaces | proved | S3b | D |
| C1 | `validIn` at an HTML element name unfolds as before | equation | proved | S3b | D |
| C2 | `validIn` at a name that is no HTML element and not `svg` is false | equation | proved | S3b | D |
| C3 | `explain c n = none ↔ validIn c n = true` | located refusal | proved, as W1 | S3c | D |
| C4 | a refusal's path names a node of the tree | located refusal | proved | S3c | D |
| P1 | the decoder inverts the printer on every well-formed tree, SVG included | exact embedding | proved | S3d | D, P |
| P2 | no delimiter character of a text node survives in the SVG namespace | escaping | proved, from `escape_no_delim` | S3d | P |
| P3 | the printer is injective on well-formed trees, SVG included | corollary of P1 | proved | S3d | D, P |
| V1 | `read (print v) = some v`, for each grammar | retraction | proved: generic, with one `decide` per grammar | S4a, S4b | P |
| V2 | `check (print v) = true`, for each grammar | corollary of V1 | proved | S4b | P |
| V3a | a string that `read` accepts is in the language of the description's expression | soundness of the reader | proved, generic | S4a | P |
| V3b | `read` accepts every string of that language | completeness of the reader | open: per grammar, with the chapter's examples as finite evidence | S4b | P |

**What the graph does not establish.**

- No parser exists in this package (ruling HP-8). N2, N3 and T2 are facts about names and about
  the seam's own automaton. They do not say that a browser parses a printed tree back to the
  same tree. P1 is about the package's decoder, which reads the printer's output alone.
- C1 and C2 bound the change to `validIn`. They do not say that the HTML checker is the
  standard's content model: that edge is the HTML package's, and it is open (debt D57).
- The content model of SVG is the definitions' index. A sentence of a chapter that narrows a
  model is not read, apart from the four of SV-4.
- The expression of a grammar is the seat's transcription of the chapter's BNF. No gate
  compares the two languages. V3a ties the reader to the transcription, not to the chapter.
- V1 says that a printed value reads back. It does not say that a browser draws it as intended.
- V3b is open. Until it is proved, the completeness of the reader against the expression rests on finite examples.
- CSS in a `style` element or attribute is never checked.

### 6.1 Debts of the HTML package

The review holds the HTML package to the same standard. None of these blocks S3 or S4. Each is
a debt of `COORDINATION.md` (ruling R-S6):

| Debt | What is owed |
| --- | --- |
| H-C1 | Exclusions as a mask. Today they are fifteen `Bool` fields, and four functions repeat the list of rules. |
| H-C2 | The class `Universe` and its reflection lemma for the HTML universes, in a home both schemas import. |
| H-C3 | Proof style: every `simp` names its lemmas, and no `simp_all`. |
| H-C4 | The tactic's hand reader of a context, after H-C1. |
| H-C5 | One set of character helpers in place of `spanChars`, `spanWhile` and two `isNameChar`. |
| H-C6 | The HTML name tables through `NameTable` (T6). |

## 7. Decisions

The owner ruled on 2026-10-11, as `docs/research/2026-10-11-svg-owner-rulings.md` relays. Ruling
R-S6 of `COORDINATION.md` records it.

1. **The nine extra files of the pin** (§2) are accepted. The pin stays thirteen files.
2. **SV-8, `desc`.** Its children are checked as phrasing content, as those of `title` are.
3. **SV-20, the strict ceiling.** `Whatwg.Svg` is strict from its first module.
4. **SV-26, the CSS pin.** One commit of `w3c/csswg-drafts`, and only the CSS Transforms 1
   source. S4c seals it.
5. **The model** is the review's sections 2 to 4, and SV-22 to SV-25 are rulings.
6. **The order** is the review's section 8: S3 in five parts, then S4 in three.

The seat decided what the review left open. §3.1 marks each as **Seat**:

- the SVG position holds two models and no exclusion set;
- `a` removes `a` from its own model, and excludes no descendant;
- a foreign tag has no markup name;
- a name table's reader checks a generated guess;
- an element of no schema is refused everywhere (SV-27);
- `validIn` becomes the walk's run, unless the benchmark refuses it.

**The slice after S4** is in lean4-effect4's repository: it moves its pin to this branch and
builds its pictures as trees.

## 8. Ledger

| Slice | Commit | Result |
| --- | --- | --- |
| S0 | `e74dc0d` on `html/svg`, 2026-10-11 | `origin/html-h7` merged; the record is ruling R-S2 of `COORDINATION.md` and the last ledger row of `docs/HTML-PACKAGE-PLAN.md` |
| S1 | `9266dac`, 2026-10-11 | the pin `vendor/w3c-svgwg-47e645ef/`, thirteen files; every file matches its upstream blob hash; `lake exe whatwg_vendorseal` passes; the seal's digests equal those of `Get-FileHash`; this plan |
| S2 | `10c81a3`, 2026-10-11 | `lake exe whatwg_svgdefinitions`: four projections and four generated modules, byte-identical to a regeneration; 63 tags, 17 element categories, 321 attribute names, 16 attribute categories, four read sentences, ten dangling names; `Whatwg.Svg` strict with no exception; two batteries; the record is ruling R-S4 of `COORDINATION.md` |
| revision | `f5201b8`, 2026-10-11 | the owner adopted the seat's review: sections 3.1, 4, 5.2, 5.3 and 6 rewritten on its model; SV-22 to SV-27; the record is ruling R-S6 of `COORDINATION.md` |
| S3a | `ab1ed31`, 2026-10-11 | `Whatwg/Svg/Data/`: `Universe`, `Mask` and `NameTable` with U1, B1 and the generic half of N1; the schema regenerated with every set a mask; `Whatwg/Svg/Schema/Universe.lean`: four instances, two exact name tables (N1), three resolution laws (K1); `Whatwg/Svg/Content/Context.lean`: the position of T3, its transition and one node's judgments; two batteries; `Whatwg.Svg` strict with no exception; the record is ruling R-S7 of `COORDINATION.md` |
| packet | `7166a6f`, 2026-10-11 | the theory packet's README; section 3.2 and the corrections to T1 and T4; the record is ruling R-S8 |
| S3b | 2026-10-11, the commit after `7166a6f` | `Whatwg/Html/Node/Walk.lean` with W1 and W2; the HTML gate reads the foreign tags and the parser's tables; the seam `Whatwg/Html/Svg.lean` with T2, X1, N2 and N3; `validIn` as the run of `check` with C1, C2 and X2; the graph `SVG-PG-SEAM` opens and debt D78 is paid; the record is ruling R-S9 |
