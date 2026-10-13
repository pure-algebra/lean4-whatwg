import Whatwg.Html.Content.Structure.Sheet
import Whatwg.Html.Content.Structure.Sheet.Laws
import WhatwgTest.Css.Parse
import WhatwgTest.Html.SheetFacts

/-!
# WhatwgTest.Html.PageSheet

The stylesheet of lean4-effect4's pages as one typed value of
`Whatwg/Html/Content/Structure/Sheet.lean` (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entry W14
of `docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at `6ad8f7b8d`:
`tools/Tools/Document/page.css`, 80 rules, which `WhatwgTest/Css/ParseCorpus.lean` holds as a
text. Its coordinator writes its port from this file.

- **The consumer's own types.** `PageToken`, the custom properties that the sheet reads, by
  kind, with their names (`Look PageToken`). `PageFact`, what the sheet draws beyond the
  package's `Fact`: one constructor for each fact that a comment of the file names. A fact of
  the sheet is a fact of either: `Fact ⊕ PageFact`.
- **Emphasis.** `emphasis : Status → Tone` is an ordinary function, and `emphasised` makes the
  rules of one: the file's one rule of three statuses is its value at this function.
- **`page`**: the 80 rules as 80 entries, in the file's order, in ten sheets in a row. Every
  rule of the file fits. Outside the three faces, which define a family by its name, no colour
  and no family is written in it: a colour is a `Paint` of a token, a family a family token.
- **The typed sheet beside the consumer's text.** The tree of `page` against
  `parseStylesheetText` of the file, rule by rule. The 247 declarations are the same, in order.
  77 rules are one tree with the file's rule, white space included. Three differ in their
  selector alone, each in its own way, stated below.
- **The round trip, by theorem.** The printed sheet parses to its tree
  (`Sheet.parse_text`), with the premise closed by the kernel. The file's own tree was made by
  the parser, and `WhatwgTest/Css/Parse.lean` could only evaluate the same of it.
- **Against pages**: the rules that draw nothing on a sample page, and the package's facts that
  the sheet does not draw.
- **Readers** of the laws, **the spellings** of each constructor of a place, and **controls**:
  a literal colour that does not type, an entry whose fact no page of the sample shows, a
  selector that is writable and that the parser does not read back as a rule.

What this battery does not claim: that a selector of the sheet selects in a browser the elements
of its fact. Selectors is not sealed here, and the spellings are from memory; the header of
`Whatwg/Html/Content/Structure/Selector.lean` lists the cases a host check should try.
-/

namespace WhatwgTest.Html.PageSheet

open Whatwg.Html
open Whatwg.Html.Content.Structure
open Whatwg.Css.Syntax

/-! ## The consumer's look: its tokens by kind -/

/-- The custom properties that the page's rules read. The first three colours, the four
families and the seven others after them are the look's (`--e4-*`, set on the root by
`Tools.View.Tokens.declarations`). `band` and `quiet`, the scale and the three measures are the
page's own, defined on the root from the look's. -/
inductive PageToken : Kind → Type where
  | ground : PageToken .colour
  | ink : PageToken .colour
  | rule : PageToken .colour
  | band : PageToken .colour
  | quiet : PageToken .colour
  | name : PageToken .family
  | data : PageToken .family
  | label : PageToken .family
  | title : PageToken .family
  | tone : PageToken .other
  | labelStyle : PageToken .other
  | titleWeight : PageToken .other
  | dataWeight : PageToken .other
  | stroke : PageToken .other
  | frame : PageToken .other
  | radius : PageToken .other
  | ratio : PageToken .other
  /-- A step of the modular scale: `--s0`, `--s1`, `--s-1`. -/
  | step (n : Int) : PageToken .other
  | measure : PageToken .other
  | margin : PageToken .other
  | gap : PageToken .other

instance : Look PageToken where
  property
    | .ground => "e4-color-ground"
    | .ink => "e4-color-ink"
    | .rule => "e4-color-rule"
    | .band => "band"
    | .quiet => "quiet"
    | .name => "e4-font-name-family"
    | .data => "e4-font-data-family"
    | .label => "e4-font-label-family"
    | .title => "e4-font-title-family"
    | .tone => "e4-tone-band"
    | .labelStyle => "e4-font-label-style"
    | .titleWeight => "e4-font-title-weight"
    | .dataWeight => "e4-font-data-weight"
    | .stroke => "e4-stroke-rule"
    | .frame => "e4-stroke-frame"
    | .radius => "e4-stroke-radius"
    | .ratio => "ratio"
    | .step n => "s" ++ toString n
    | .measure => "measure"
    | .margin => "margin"
    | .gap => "gap"

/-! ## The consumer's facts -/

/-- The word of a status (`Tools.Document.Html.inline`, the case `status`). -/
inductive Status where
  | proved
  | modulo
  | goal
  | «open»
  | refuted
  | absent
  | assumed
  | missing
  deriving DecidableEq, Repr

def Status.word : Status → String
  | .proved => "proved"
  | .modulo => "modulo"
  | .goal => "goal"
  | .«open» => "open"
  | .refuted => "refuted"
  | .absent => "absent"
  | .assumed => "assumed"
  | .missing => "missing"

def Status.all : List Status :=
  [.proved, .modulo, .goal, .«open», .refuted, .absent, .assumed, .missing]

def Status.test (status : Status) : Test := .valued "data-status" status.word

/-- A part of a page that holds pieces. -/
inductive Region where
  | contents
  | crumbs
  | pager
  | footer
  | graph
  | cell
  | nav
  deriving DecidableEq, Repr

def Region.test : Region → Test
  | .contents => .classed "toc"
  | .crumbs => .classed "crumbs"
  | .pager => .classed "pager"
  | .footer => .named "footer"
  | .graph => .and (.named "figure") (.classed "graph")
  | .cell => .named "td"
  | .nav => .named "nav"

/-- A piece inside a region. -/
inductive Piece where
  | label
  | item
  | list
  | bullets
  | link
  | scroll
  | picture
  | code
  deriving DecidableEq, Repr

def Piece.test : Piece → Test
  | .label => .classed "label"
  | .item => .named "li"
  | .list => .named "ol"
  | .bullets => .named "ul"
  | .link => .named "a"
  | .scroll => .classed "scroll"
  | .picture => .named "svg"
  | .code => .named "code"

/-- What a `details` folds away. -/
inductive Fold where
  | statement
  | words
  | diagram
  deriving DecidableEq, Repr

def Fold.word : Fold → String
  | .statement => "statement"
  | .words => "words"
  | .diagram => "diagram"

/-- One of several tests. -/
def anyOf : List Test → Test
  | [] => .not .any
  | [t] => t
  | t :: rest => .or t (anyOf rest)

/-- What the consumer's sheet draws beyond the package's facts: one constructor for each fact
that a comment of `page.css` names. -/
inductive PageFact where
  /-- Every element. -/
  | everything
  /-- The page: its `body`. -/
  | page
  /-- The parts of the page, beside the content. -/
  | contents
  /-- The way past the navigation. -/
  | skip
  /-- A label: a name of a kind of thing. -/
  | label
  /-- The site's name. -/
  | home
  /-- A piece inside a region: the items of the contents, the links of the pager. -/
  | part (region : Region) (piece : Piece)
  /-- The site's sections, in its header. -/
  | sections
  /-- The second level of the contents. -/
  | nested
  /-- A crumb after the first: a separator stands before it. -/
  | laterCrumb
  /-- The neighbours in reading order. -/
  | pager
  /-- The link to the next page. -/
  | pagerNext
  /-- A heading. -/
  | title
  /-- A heading of one level. -/
  | heading (level : Nat)
  /-- The heading of a part at the top of the page: its rule is the part's boundary. -/
  | topPart
  /-- The heading of a part below the page's own. -/
  | partTitle
  /-- A part's key beside its title. -/
  | key
  /-- Prose, held to its measure. -/
  | prose
  | paragraph
  | link
  /-- Text in a language, in a line or in a block. -/
  | code
  /-- A `details` of a kind, its summary, and the code in the summary of a statement. -/
  | fold (kind : Fold)
  | foldSummary (kind : Fold)
  | statementCode
  | anyFold
  /-- Fields: a label and its value. -/
  | fields
  | fieldValue
  /-- A region that scrolls sideways, by its class. -/
  | scroll
  | table
  | row
  | cell
  /-- The first cell of a row of the body: an identity. -/
  | firstCell
  /-- A status, one of several statuses, and one status. -/
  | anyStatus
  | statuses (among : List Status)
  | status (status : Status)
  /-- A figure of a graph, and a caption. -/
  | graph
  | caption
  | footer
  /-- The line of the footer before its last: a gap stands above it. -/
  | footerGap
  | navigation
  deriving DecidableEq, Repr

def PageFact.place : PageFact → Where
  | .everything => .here .any
  | .page => .here (.named "body")
  | .contents => .under (.here (.named "main")) (.classed "toc")
  | .skip => .here (.classed "skip")
  | .label => .here (.or (.classed "label") (.or (.named "dt") (.named "summary")))
  | .home => .here (.classed "home")
  | .part region piece => .inside (.here region.test) piece.test
  | .sections => .inside (.inside (.here (.named "header")) (.named "nav")) (.named "ol")
  | .nested => .inside (.inside (.here (.classed "toc")) (.named "ol")) (.named "ol")
  | .laterCrumb => .inside (.here (.classed "crumbs")) (.and (.named "li") (.not .first))
  | .pager => .here (.classed "pager")
  | .pagerNext => .inside (.here (.classed "pager")) (.and (.named "a") (.valued "rel" "next"))
  | .title => .here Whatwg.Html.Content.Structure.heading
  | .heading level => .here (.named ("h" ++ toString level))
  | .topPart => .under (.here (.named "section")) (.named "h2")
  | .partTitle => .under (.here (.named "section")) (Test.oneOf ["h2", "h3", "h4", "h5", "h6"])
  | .key => .here (.classed "key")
  | .prose => .here (Test.oneOf ["p", "dd", "li", "figcaption"])
  | .paragraph => .here (.named "p")
  | .link => .here (.named "a")
  | .code => .here (Test.oneOf ["code", "pre"])
  | .fold kind => .here (.and (.named "details") (.classed kind.word))
  | .foldSummary kind =>
    .under (.here (.and (.named "details") (.classed kind.word))) (.named "summary")
  | .statementCode =>
    .inside (.under (.here (.and (.named "details") (.classed "statement"))) (.named "summary"))
      (.named "code")
  | .anyFold => .here (.named "details")
  | .fields => .here (.named "dl")
  | .fieldValue => .here (.named "dd")
  | .scroll => .here (.classed "scroll")
  | .table => .here (.named "table")
  | .row => .here (.named "tr")
  | .cell => .here (.or (.named "th") (.named "td"))
  | .firstCell => .here (.and (.named "td") .first)
  | .anyStatus => .here (.classed "status")
  | .statuses among => .here (.and (.classed "status") (anyOf (among.map Status.test)))
  | .status which => .here (.and (.classed "status") which.test)
  | .graph => .here (.and (.named "figure") (.classed "graph"))
  | .caption => .here (.named "figcaption")
  | .footer => .here (.named "footer")
  | .footerGap => .inside (.here (.named "footer")) (.and (.named "li") (.nthLast 2))
  | .navigation => .here (.named "nav")

instance : Vocabulary PageFact := ⟨PageFact.place⟩

/-- A fact of the sheet: the package's, or the consumer's. -/
abbrev SheetFact := Fact ⊕ PageFact

abbrev Page := Sheet SheetFact PageToken

/-- A rule that draws a fact of the consumer's. -/
def own (fact : PageFact) (declarations : List (Decl PageToken)) (aspect : Aspect := {})
    (also : List SheetFact := []) : Entry SheetFact PageToken :=
  .draw (.inr fact) declarations aspect also

/-- A rule that draws a fact of the package's. -/
def std (fact : Fact) (declarations : List (Decl PageToken)) (aspect : Aspect := {})
    (also : List SheetFact := []) : Entry SheetFact PageToken :=
  .draw (.inl fact) declarations aspect also

/-! ## Emphasis: a function from a status to a tone -/

/-- How far a status stands out. -/
inductive Tone where
  | quiet
  | full
  deriving DecidableEq, Repr

/-- **What is proved recedes, so what is open stands out** (the comment of the rule in
`page.css`): an ordinary function. -/
def emphasis : Status → Tone
  | .proved => .quiet
  | .absent => .quiet
  | .assumed => .quiet
  | _ => .full

/-- The colour of a tone: a token of the look, and nothing else can be said here. -/
def Tone.paint : Tone → Paint PageToken
  | .quiet => .token .quiet
  | .full => .token .ink

/-- Whether the mark of a status is a circle. -/
def Status.circled : Status → Bool
  | .proved => true
  | .modulo => true
  | .goal => true
  | .«open» => true
  | _ => false

/-! ## Values -/

def tok {kind : Kind} (token : PageToken kind) : Component := Look.var token
def s (n : Int) : Component := Look.var (PageToken.step n)
def kw (name : String) : Value := [.ident name]
def rem (q : Rat) : Component := .dimension q "rem"
def em (q : Rat) : Component := .dimension q "em"
def vw (q : Rat) : Component := .dimension q "vw"
def row : List Component → Value := Value.spaced
def clamp (low middle high : Component) : Component := .call "clamp" (Value.commas [low, middle, high])
def track (width : Component) : Component := .call "minmax" (Value.commas [.int 0, width])
/-- A hairline of the look: its weight, solid, in the colour of rules. -/
def hairline (property : String) (known : takesLine property = true := by decide) : Decl PageToken :=
  .line property (tok .stroke) "solid" (.token .rule) known

/-! ## The sheet -/

def face (family file : String) (lightest heaviest : Int) (style : String) : Entry SheetFact PageToken :=
  .face [.of "font-family" [.string family],
    .of "src" [.call "url" [.string file], .space, .call "format" [.string "woff2"]],
    .of "font-weight" [.int lightest, .space, .int heaviest], .of "font-style" (kw style),
    .of "font-display" (kw "swap")]

/-- The faces, served from the site. -/
def faces : Page :=
  [face "Source Serif 4" "fonts/source-serif-4/source-serif-4-latin-opsz-normal.woff2" 200 900 "normal",
    face "Source Serif 4" "fonts/source-serif-4/source-serif-4-latin-opsz-italic.woff2" 200 900 "italic",
    face "JetBrains Mono" "fonts/jetbrains-mono/jetbrains-mono-latin-wght-normal.woff2" 100 800 "normal"]

/-- One modular scale: each step is the one before times the ratio, and the one after divided
by it. -/
def scale : List (Definition PageToken) :=
  [.other .ratio [.number 1.2], .other (.step 0) [rem 1.0625]] ++
    ([1, 2, 3, 4, 5] : List Int).map (fun n =>
      .other (.step n) [.calc (.mul (.leaf (s (n - 1))) (.leaf (tok .ratio)))]) ++
    ([-1, -2] : List Int).map (fun n =>
      .other (.step n) [.calc (.div (.leaf (s (n + 1))) (.leaf (tok .ratio)))])

/-- The page's own tokens: the scale, three measures, and two colours mixed from the look's. -/
def root : Page :=
  [.define (scale ++
    [.other .measure [.dimension 66 "ch"], .other .margin [rem 15],
      .other .gap [clamp (s 1) (vw 3) (s 4)],
      .colour .band (.mix (.token .rule) (.tone .tone) (.token .ground)),
      .colour .quiet (.mix (.token .ink) (.percent 64) (.token .ground))])]

/-- The frame: the site's header, the content with a margin at its right, the footer. -/
def frame : Page :=
  [own .everything [.plain "box-sizing" (kw "border-box")],
    own .page [.plain "margin" [.int 0], .colour "background" (.token .ground),
      .colour "color" (.token .ink), .font [s 0, .delim '/', .number 1.55] .name,
      .plain "font-optical-sizing" (kw "auto"), .plain "text-rendering" (kw "optimizeLegibility"),
      .plain "-webkit-font-smoothing" (kw "antialiased")],
    own .page [.plain "display" (kw "grid"),
      .plain "grid-template-columns"
        (row [track (.dimension 1 "fr"), track (rem 58), tok .margin, track (.dimension 1 "fr")]),
      .plain "column-gap" [tok .gap], .plain "padding" (row [.int 0, clamp (s 0) (vw 4) (s 3)])],
    std .pageHeader [.plain "grid-column" (row [.int 2, .delim '/', .int 4])] {} [.inl .pageFooter],
    std .main [.plain "grid-column" [.int 2], .plain "min-width" [.int 0]],
    own .contents [.plain "float" (kw "right"), .plain "clear" (kw "right"),
      .plain "width" [tok .margin],
      .plain "margin-right"
        [.calc (.mul (.leaf (.int (-1))) (.add (.leaf (tok .margin)) (.leaf (tok .gap))))],
      .plain "position" (kw "sticky"), .plain "top" [.int 0],
      .plain "max-height" [.dimension 100 "vh"], .plain "overflow-y" (kw "auto"),
      .plain "padding" (row [s 0, .int 0]), .plain "font-size" [s (-1)],
      .plain "line-height" [.number 1.35]],
    .media (Prelude.feature "max-width" [rem 64])
      [own .page [.plain "display" (kw "block")],
        own .contents [.plain "float" (kw "none"), .plain "width" (kw "auto"),
          .plain "margin" (row [s 0, .int 0, s 1]), .plain "position" (kw "static"),
          .plain "max-height" [rem 14], .plain "padding" (row [s (-1), s 0]), hairline "border",
          .plain "border-radius" [tok .radius]]]]

/-- The way past the navigation, labels, the navigations and the site's header. -/
def navigation : Page :=
  [own .skip [.plain "position" (kw "absolute"), .plain "left" [vw (-100)]],
    own .skip [.plain "position" (kw "static"), .plain "display" (kw "inline-block"),
      .plain "margin" (row [s (-1), .int 0])] { state := some "focus" },
    own .label [.family .label, .plain "font-style" [tok .labelStyle]],
    own (.part .nav .list) [.plain "padding" [.int 0], .plain "margin" [.int 0],
      .plain "list-style" (kw "none")],
    std .current [.plain "text-decoration-thickness" [.px 2]],
    std .currentPage [.plain "font-weight" (kw "bolder"), .plain "text-decoration" (kw "none")],
    std .pageHeader [.plain "display" (kw "flex"), .plain "flex-wrap" (kw "wrap"),
      .plain "align-items" (kw "baseline"), .plain "gap" (row [s (-1), s 3]),
      .plain "padding" (row [s 2, .int 0, s 0]), .plain "margin-bottom" [s 2],
      hairline "border-bottom"],
    own .home [.family .title, .plain "font-weight" (kw "bolder"), .plain "font-size" [s 1],
      .plain "text-decoration" (kw "none")],
    own .sections [.plain "display" (kw "flex"), .plain "flex-wrap" (kw "wrap"),
      .plain "gap" (row [s (-2), s 1])],
    own (.part .contents .label) [.plain "margin" (row [.int 0, .int 0, s (-1)])],
    own (.part .contents .item) [.plain "margin" (row [s (-2), .int 0])],
    own .nested [.plain "margin" (row [s (-2), .int 0, s (-1), s 0])],
    own (.part .contents .link) [.plain "text-decoration" (kw "none")],
    own (.part .contents .link) [.plain "text-decoration" (kw "underline")] { state := some "hover" },
    own (.part .crumbs .list) [.plain "display" (kw "flex"), .plain "flex-wrap" (kw "wrap"),
      .plain "gap" [s (-2)], .plain "font-size" [s (-1)]],
    own .laterCrumb [.plain "content" [.string "/"],
      .plain "content" (row [.string "/", .delim '/', .string ""]),
      .plain "margin-right" [s (-2)], .colour "color" (.token .quiet)] { part := some "before" },
    own .pager [.plain "display" (kw "flex"), .plain "gap" [s 0],
      .plain "margin" (row [s 4, .int 0, .int 0]), .plain "padding-top" [s 0],
      hairline "border-top"],
    own (.part .pager .link) [.plain "display" (kw "flex"), .plain "flex-direction" (kw "column"),
      .plain "max-width" [.percent 48], .plain "text-decoration" (kw "none")],
    own .pagerNext [.plain "margin-left" (kw "auto"), .plain "text-align" (kw "right")],
    own (.part .pager .label) [.plain "font-size" [s (-1)], .colour "color" (.token .quiet)]]

/-- Headings, a part's key, and prose at its measure. -/
def headings : Page :=
  [own .title [.family .title, .plain "font-weight" [tok .titleWeight],
      .plain "line-height" [.number 1.15], .plain "scroll-margin-top" [s 0],
      .plain "text-wrap" (kw "balance")],
    own (.heading 1) [.plain "font-size" [clamp (s 3) (vw 5) (s 5)],
      .plain "margin" (row [s (-1), .int 0, s 0])],
    own (.heading 2) [.plain "font-size" [s 3]],
    own (.heading 3) [.plain "font-size" [s 2]],
    own (.heading 4) [.plain "font-size" [s 1]] {} [.inr (.heading 5), .inr (.heading 6)],
    own (.heading 3) [.plain "margin" (row [s 3, .int 0, s (-1)])] {}
      [.inr (.heading 4), .inr (.heading 5), .inr (.heading 6)],
    own .topPart [.plain "margin-top" [s 4], .plain "padding-top" [s 0], hairline "border-top"],
    own .partTitle [.plain "text-decoration" (kw "underline"),
      .plain "text-decoration-thickness" [.px 2], .plain "text-underline-offset" [em 0.2]]
      { state := some "target", above := 1 },
    own .key [.plain "margin-left" [em 0.6],
      .font [tok .dataWeight, .space, s (-2), .delim '/', .int 1] .data,
      .colour "color" (.token .quiet), .plain "text-decoration" (kw "none"),
      .plain "white-space" (kw "nowrap"), .plain "vertical-align" [em 0.15]],
    own .key [.colour "color" (.token .ink), .plain "text-decoration" (kw "underline")]
      { state := some "hover" },
    own .prose [.plain "max-width" [tok .measure], .plain "overflow-wrap" (kw "anywhere")],
    own .paragraph [.plain "margin" (row [s (-1), .int 0])],
    own .link [.colour "color" .inherit, .plain "text-underline-offset" [em 0.15]],
    own .everything [.line "outline" (.px 3) "solid" (.token .ink), .plain "outline-offset" [.px 2]]
      { state := some "focus-visible" }]

/-- Code, a long statement folded under its first line, and fields. -/
def code : Page :=
  [own .code [.family .data, .plain "font-size" [em 0.88],
      .plain "font-variant-ligatures" (kw "none")],
    std .codeSpan [.colour "background" (.token .band), .plain "padding" (row [em 0.05, em 0.3]),
      .plain "border-radius" [tok .radius], .plain "overflow-wrap" (kw "anywhere")],
    std .block [.colour "background" (.token .band), hairline "border",
      .plain "border-radius" [tok .radius], .plain "padding" (row [s (-1), s 0]),
      .plain "white-space" (kw "pre-wrap"), .plain "overflow-wrap" (kw "anywhere"),
      .plain "line-height" [.number 1.45]],
    own (.fold .statement) [.plain "margin" (row [s (-1), .int 0])],
    own (.foldSummary .statement) [.plain "cursor" (kw "pointer")],
    own .statementCode [.plain "font-style" (kw "normal")],
    own .fields [.plain "display" (kw "grid"),
      .plain "grid-template-columns" (row [.ident "max-content", .dimension 1 "fr"]),
      .plain "gap" (row [s (-2), s 0])],
    own .fieldValue [.plain "margin" [.int 0]]]

/-- A double rule of the look: twice the weight of a hairline. -/
def doubleRule (property : String) (known : takesLine property = true := by decide) : Decl PageToken :=
  .line property (.calc (.mul (.leaf (.int 2)) (.leaf (tok .stroke)))) "solid" (.token .rule) known

/-- A region that scrolls sideways, and a table after the booktabs rules. -/
def tables : Page :=
  [own .scroll [.plain "overflow-x" (kw "auto"), .plain "margin" (row [s 1, .int 0])],
    own .table [.plain "border-collapse" (kw "collapse"), .plain "width" [.percent 100],
      .plain "min-width" [rem 36], .plain "font-size" [s (-1)], .plain "line-height" [.number 1.35],
      .plain "font-variant-numeric" (row [.ident "tabular-nums", .ident "lining-nums"]),
      doubleRule "border-top", doubleRule "border-bottom"],
    own .cell [.plain "text-align" (kw "left"), .plain "vertical-align" (kw "top"),
      .plain "padding" (row [s (-2), s (-1)])],
    std .tableHead [.family .label, .plain "font-style" [tok .labelStyle],
      .plain "font-weight" (kw "inherit"), hairline "border-bottom"],
    std .bodyCell [.plain "padding-top" [s (-1)], .plain "padding-bottom" [s (-1)]],
    own .firstCell [.plain "white-space" (kw "nowrap")],
    own (.part .cell .code) [.colour "background" .clear, .plain "padding" [.int 0],
      .plain "overflow-wrap" (kw "normal")]]

/-- The mark of a status, before its word. -/
def mark (status : Status) (declarations : List (Decl PageToken)) : Entry SheetFact PageToken :=
  own (.status status) declarations { part := some "before" }

/-- **The rules of an emphasis**: one for each tone but the page's own ink, drawing the statuses
of that tone in its colour. A tone that no status takes has no rule. -/
def emphasised (emphasis : Status → Tone) : Page :=
  [Tone.quiet].filterMap fun tone =>
    match Status.all.filter (fun status => emphasis status == tone) with
    | [] => none
    | among => some (own (.statuses among) [.colour "color" tone.paint])

/-- A status: its emphasis, a function from a status to a tone, and its mark. -/
def statuses : Page :=
  [own .anyStatus [.plain "white-space" (kw "nowrap")]] ++ emphasised emphasis ++
  [own (.statuses (Status.all.filter Status.circled))
      [.plain "content" [.string ""], .plain "display" (kw "inline-block"),
        .plain "box-sizing" (kw "border-box"), .plain "width" [em 0.7], .plain "height" [em 0.7],
        .plain "margin-right" [em 0.35], .plain "vertical-align" [em (-0.05)],
        .line "border" (tok .frame) "solid" .current, .plain "border-radius" [.percent 50],
        .plain "-webkit-print-color-adjust" (kw "exact"), .plain "print-color-adjust" (kw "exact"),
        .plain "forced-color-adjust" (kw "none")] { part := some "before" },
    mark .proved [.colour "background" .current],
    mark .modulo [.colour "background" .current, .plain "background-clip" (kw "content-box"),
      .plain "padding-right" [.calc (.sub (.leaf (em 0.35)) (.leaf (tok .frame)))]],
    mark .«open» [.plain "border-style" (kw "dashed")],
    mark .refuted [.plain "content" [.string "×"],
      .plain "content" (row [.string "×", .delim '/', .string ""]),
      .plain "display" (kw "inline-block"), .plain "width" [em 0.7],
      .plain "margin-right" [em 0.35], .plain "text-align" (kw "center")]]

/-- A figure with its caption and the figure in words, and the footer. -/
def figures : Page :=
  [own .graph [.plain "margin" (row [s 2, .int 0, s (-1)])],
    own (.part .graph .scroll) [.noLine "border", .plain "margin" [.int 0]],
    own (.part .graph .picture) [.plain "display" (kw "block"), .plain "max-width" (kw "none"),
      .plain "height" (kw "auto")],
    own .caption [.plain "margin-top" [s (-1)], .plain "font-size" [s (-1)]],
    own (.fold .words) [.plain "margin" (row [.int 0, .int 0, s 2]), .plain "font-size" [s (-1)]],
    own (.foldSummary .words) [.plain "cursor" (kw "pointer")] {} [.inr (.foldSummary .diagram)],
    own (.fold .diagram) [.plain "margin" (row [s 0, .int 0])],
    own .footer [.plain "margin-top" [s 4], .plain "padding" (row [s 0, .int 0, s 3]),
      hairline "border-top", .plain "font-size" [s (-1)]],
    own (.part .footer .label) [.plain "margin" (row [.int 0, .int 0, s (-2)])],
    own (.part .footer .bullets) [.plain "list-style" (kw "none"), .plain "margin" [.int 0],
      .plain "padding" [.int 0]],
    own (.part .footer .item) [.plain "max-width" (kw "none"), .plain "overflow-wrap" (kw "anywhere")],
    own .footerGap [.plain "margin-top" [s (-2)]]]

/-- On paper: nothing scrolls, nothing breaks inside a block, and the navigation is left out. -/
def print : Page :=
  [.media [.ident "print"]
    [own .scroll [.plain "overflow" (kw "visible"), .noLine "border"],
      own .table [.plain "min-width" [.int 0]],
      std .block [.plain "break-inside" (kw "avoid")] {} [.inr .row, .inr .fields, .inr .anyFold],
      own (.heading 2) [.plain "break-after" (kw "avoid")] {} [.inr (.heading 3), .inr (.heading 4)],
      own .skip [.plain "display" (kw "none")] {} [.inr .navigation]]]

/-- **`page.css` as one typed value**: 80 entries, one for each of its rules, in its order. -/
def page : Page :=
  faces ++ root ++ frame ++ navigation ++ headings ++ code ++ tables ++ statuses ++ figures ++ print

/-! ## The real text beside it -/

/-- The consumer's file, parsed. -/
def read : Stylesheet := parseStylesheetText WhatwgTest.Css.ParseCorpus.pageCss

/-- The tree of the typed sheet. -/
def written : Stylesheet := page.stylesheet

/-- The text of a rule's prelude, with no white space at its ends. -/
def preludeText (r : Rule) : String := Prelude.text (Css.Rule.prelude r)

/-- The rules of the two trees that are not one rule, each by its place and the two preludes:
the typed sheet's first. -/
def differing : List (Nat × String × String) :=
  ((written.rules.zip read.rules).zipIdx.filter fun pair => pair.1.1 != pair.1.2).map fun pair =>
    (pair.2, preludeText pair.1.1, preludeText pair.1.2)

/-! ## The typed sheet beside the consumer's text -/

-- One entry for each rule of the file, and one rule for each entry.
#guard page.length == 80
#guard written.rules.length == 80 && read.rules.length == 80

-- The declarations of the two trees are the same 247, in the order they stand: no value is
-- spelled another way in the tree, and none is missing.
#guard written.located.length == 247
#guard written.located.map (·.declaration) == read.located.map (·.declaration)

-- Rule by rule, the two trees have the same at-rule name, the same declarations and the same
-- rules inside. So two rules that are not one rule differ in their prelude and in nothing else.
#guard (written.rules.zip read.rules).all fun pair =>
  Css.Rule.name? pair.1 == Css.Rule.name? pair.2 && Css.Rule.decls pair.1 == Css.Rule.decls pair.2 &&
    Css.Rule.rules pair.1 == Css.Rule.rules pair.2

-- 77 of the 80 rules are one tree with the rule of the file, the white space of a prelude
-- included. These three are not: each by its place, with the typed sheet's selector and the
-- file's.
#guard differing ==
  [(26, ".crumbs li:not(:first-child)::before", ".crumbs li + li::before"),
    (38,
      "section:target > h2, section:target > h3, section:target > h4, section:target > h5, section:target > h6",
      "section:target > :is(h2, h3, h4, h5, h6)"),
    (44, "*:focus-visible", ":focus-visible")]

-- The three ways in which a selector differs.
--
-- 1. A place has no sibling combinator. The file's `li + li` is a crumb after the first, which
--    is `li:not(:first-child)` here (26). The two select the same items of a list whose element
--    children are all `li`.
-- 2. An `or` at the top of a place's own test is a comma, so that each alternative has its own
--    weight, and the place above is written once for each (38). The file writes `:is()` there.
-- 3. Every element in a state is `*` with the state (44). The file leaves the `*` out.
--
-- The order of the rules is the file's: `page` is written in it.

/-! ## The text that the package prints -/

-- 80 lines, one rule a line. The text differs from the file's where the tree does not: a number
-- has its zero (`0.2em` for the file's `.2em`), a block has no semicolon after its last
-- declaration, a run of white space is one space, and a comment is gone.
#guard (page.text.splitOn "\n").length == 80
-- It is 77 code points longer than the lines of the file's tree: the three selectors.
#guard page.text.length == 8430
#guard read.lines.length == 8353
#guard (page.text.splitOn "\n")[4]? == some "* { box-sizing: border-box }"
#guard (page.text.splitOn "\n")[38]? == some
  ("section:target > h2, section:target > h3, section:target > h4, section:target > h5, section:target > h6 " ++
    "{ text-decoration: underline; text-decoration-thickness: 2px; text-underline-offset: 0.2em }")

/-! ## The round trip, by theorem -/

-- Reader of `Sheet.parse_text` at the consumer's sheet: the text that the package prints of it
-- parses to its tree. The premise is `Sheet.writable page`, and the kernel computes it: the
-- sheet is written as data, so nothing of it was made by the parser.
example : parseStylesheetText page.text = page.stylesheet :=
  Sheet.parse_text page (by decide +kernel)

-- The consumer's check, ported onto the tree in `WhatwgTest/Css/Parse.lean`, finds nothing in
-- the tree of the typed sheet. The types leave it two places to look: a plain value and a face.
#guard (written.located.filterMap WhatwgTest.Css.Parse.problem).isEmpty

/-! ## Every style rule names its fact -/

-- Reader of `Sheet.styleRules_stylesheet`: the style rules of the tree, those under a condition
-- too, are the rules of the sheet's sources.
example : styleRulesAll written.rules = page.sources.map (·.2) := Sheet.styleRules_stylesheet page

-- Reader of `Sheet.rule_of_source`: each of them is the rule under the selector of its facts, or
-- the root's.
example (pair : Source SheetFact × Rule) (h : pair ∈ page.sources) :
    Source.Rules PageToken pair.1 pair.2 :=
  Sheet.rule_of_source page h

-- The file's tree has 82 style rules, seven of them under a condition, and the sheet has 82
-- sources. One draws no fact and says so: the root's tokens. The 81 others draw 94 facts.
#guard (styleRulesAll read.rules).length == 82
#guard page.sources.length == 82
#guard (page.sources.filter fun pair => pair.1.drawn.isEmpty).length == 1
#guard page.facts.length == 94

/-! ## Against pages -/

/-- A page of the consumer's nodes (`WhatwgTest/Html/SheetFacts.lean`): a part with a
paragraph, a table in its region, a block of code, the three navigations and the footer. -/
def sample : RawNode := WhatwgTest.Html.SheetFacts.page

-- The rules of the sheet that draw nothing on the sample page, by their selectors: it has no
-- skip link, one level of contents, no heading below `h2`, no fold, no fields, no figure, and
-- two of the four statuses whose mark has a rule of its own.
#guard ((page.unused [sample]).eraseDups.map fun fact => (selectorOf fact).text) ==
  [".skip", ".toc ol ol", ".pager .label", "h3", "h4", "h5", "h6", "details.statement",
    "details.statement > summary", "details.statement > summary code", "dl", "dd",
    ".status[data-status=modulo]", ".status[data-status=refuted]", "figure.graph",
    "figure.graph .scroll", "figure.graph svg", "figcaption", "details.words",
    "details.words > summary", "details.diagram > summary", "details.diagram", "details"]

-- A second page, a figure with its words folded beneath, shows two more: a caption and a
-- `details`.
#guard ((page.unused [sample, WhatwgTest.Html.SheetFacts.figure]).eraseDups.length) == 21

-- Control: an entry whose fact no page of the sample shows. The sample has a proved status and
-- an open one, and no refuted one.
#guard Sheet.unused [mark .refuted [.plain "content" [.string "×"]]] [sample] ==
  [.inr (.status .refuted)]
#guard Sheet.unused [mark .proved [.colour "background" .current]] [sample] == []

-- The package's facts that the consumer's sheet does not draw: it draws the same structure by
-- a selector of its own (a class for the region, `td:first-child` for the head of a row, a
-- `figcaption` and a `summary` wherever they stand), and nothing for a block of code.
#guard Sheet.undrawn (Fact.all.map Sum.inl : List SheetFact) page ==
  [.inl .partHeading, .inl .rowHead, .inl .codeBlock, .inl .region, .inl .caption, .inl .summary]

-- The package's fact beside the consumer's, at the region that scrolls: two selectors, and on
-- the sample page the same places. The fact is the element with its role, which the package's
-- builder makes; the class is the consumer's name for it.
#guard (selectorOf Fact.region).text == "[role=region][tabindex]"
#guard (selectorOf PageFact.scroll).text == ".scroll"
#guard placesOfFact Fact.region sample == placesOfFact PageFact.scroll sample

-- And at the head of a row, where the package's fact is wider: a `th` too.
#guard (selectorOf Fact.rowHead).text == "tr > :is(td, th):first-child"
#guard (placesOfFact PageFact.firstCell sample).length == 2
#guard (placesOfFact Fact.rowHead sample).length == 3

/-! ## Emphasis is a function -/

-- The file's rule of the three statuses that recede is the value of `emphasised` at `emphasis`.
#guard (emphasised emphasis).text ==
  ".status:is([data-status=proved], [data-status=absent], [data-status=assumed]) " ++
    "{ color: var(--quiet) }"

-- Another function is another sheet.
#guard (emphasised fun status => if status == .refuted then .quiet else .full).text ==
  ".status[data-status=refuted] { color: var(--quiet) }"

-- Control: where every status is in the full ink there is no rule, and not a rule of no status.
#guard (emphasised fun _ => .full).length == 0

/-! ## The spellings of a place

One of each constructor, and the cases where a position changes a spelling. Each is from memory
of Selectors Level 4, and each is a case for a host check. -/

/-- The text of the selector of a place. -/
def spell (w : Where) (aspect : Aspect := {}) : String := (w.selector aspect).text

#guard spell (.here .any) == "*"
#guard spell (.here (.named "p")) == "p"
#guard spell (.here (.classed "x")) == ".x"
#guard spell (.here (.has "open")) == "[open]"
#guard spell (.here (.valued "rel" "next")) == "[rel=next]"
#guard spell (.here (.valued "title" "a \"b\"")) == "[title=\"a \\\"b\\\"\"]"
#guard spell (.here (.valued "title" "")) == "[title=\"\"]"
#guard spell (.here .first) == ":first-child"
#guard spell (.here (.nthLast 2)) == ":nth-last-child(2)"
#guard spell (.here (.not (.or (.named "a") (.classed "b")))) == ":not(a, .b)"
#guard spell (.here (.and (.named "p") (.classed "x"))) == "p.x"
#guard spell (.here (.or (.named "a") (.named "b"))) == "a, b"
#guard spell (.under (.here (.named "a")) (.named "b")) == "a > b"
#guard spell (.inside (.here (.named "a")) (.named "b")) == "a b"

-- A type selector stands first in a compound, so after another simple selector it is `:is()`;
-- `any` after another simple selector writes nothing.
#guard spell (.here (.and (.classed "x") (.named "p"))) == ".x:is(p)"
#guard spell (.here (.and .any .first)) == "*:first-child"
#guard spell (.here (.and .first .any)) == ":first-child"

-- An `or` that is not at the top of the place's own test is `:is()`.
#guard spell (.inside (.under (.here (.has "open")) (.or (.named "a") (.named "b"))) (.nthLast 1)) ==
  "[open] > :is(a, b) :nth-last-child(1)"

-- No name at all is the test that holds of nothing.
#guard spell (.here (Test.oneOf [])) == ":not(*)"

-- A name that is no plain identifier is written with its escape.
#guard spell (.here (.classed "1x")) == ".\\31 x"

-- A state is asked of the element, or of a place above it; a count past the top is the top. A
-- part is of the element.
#guard spell (.under (.here (.named "a")) (.named "b")) { state := some "hover" } == "a > b:hover"
#guard spell (.under (.here (.named "a")) (.named "b")) { state := some "hover", above := 1 } ==
  "a:hover > b"
#guard spell (.under (.here (.named "a")) (.named "b")) { state := some "hover", above := 5 } ==
  "a:hover > b"
#guard spell (.here (.named "a")) { state := some "hover", part := some "before" } ==
  "a:hover::before"

/-! ## Readers of the laws -/

-- `quiet_selectorOf`: the selector of every fact of the sheet's vocabulary, with every aspect,
-- has no comment in its text: for every status, every level of heading, every piece of every
-- region.
example (fact : SheetFact) (aspect : Aspect) : Value.quiet (selectorOf fact aspect) = true :=
  quiet_selectorOf fact aspect

-- `Where.writable_selector`: the selector of every status is writable, in every state whose
-- name is a name.
example (which : Status) (aspect : Aspect) (h : aspect.plain = true) :
    Value.writable (selectorOf (PageFact.status which) aspect) = true :=
  Where.writable_selector (by cases which <;> decide) h

-- `Sheet.text_append`, `Sheet.facts_append`: `page` is ten sheets in a row.
example : (faces ++ root).text = faces.text ++ "\n" ++ root.text :=
  Sheet.text_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

example : (frame ++ navigation).facts = frame.facts ++ navigation.facts :=
  Sheet.facts_append frame navigation

/-- A sheet over the package's facts alone. -/
def standard : Sheet Fact PageToken :=
  [.draw .tableHead [.family .label], .draw .block [.colour "background" (.token .band)]]

-- `Sheet.stylesheet_inl`: put into the sum with the consumer's facts, it has the tree it had.
example : (standard.inl : Page).stylesheet = standard.stylesheet := Sheet.stylesheet_inl standard

#guard (standard.inl : Page).text ==
  "th { font-family: var(--e4-font-label-family) }\npre { background: var(--band) }"

-- `Sheet.occurs_of_mem_unused`: a fact that `unused` answers is shown by no page given.
example (fact : SheetFact) (h : fact ∈ page.unused [sample]) :
    occurs (Vocabulary.place fact) sample = false :=
  Sheet.occurs_of_mem_unused h List.mem_cons_self

-- `Decl.carries_iff`: whatever the tone of a status, the declaration of its colour names a
-- property that carries a colour, so it is no plain one.
example (tone : Tone) : carries (Decl.colour "color" tone.paint).property = true :=
  (Decl.carries_iff _).mpr rfl

-- `Paint.quiet_value`: the two colours that the page mixes have no comment in their text,
-- whatever the names of the tokens.
example (a b : PageToken .colour) (share : PageToken .other) :
    Value.quiet (Paint.mix (.token a) (.tone share) (.token b)).value = true :=
  Paint.quiet_value _

/-! ## Controls -/

-- A literal colour does not type. `color` carries a colour, so a plain declaration may not name
-- it.
/--
error: could not synthesize default value for parameter 'free' using tactics
---
error: Tactic `decide` proved that the proposition
  carries "color" = false
is false
-/
#guard_msgs in
example : Decl PageToken := .plain "color" [.hash "fff"]

-- And the declaration of a colour takes a paint: a hash is none.
/--
error: Application type mismatch: The argument
  Component.hash "fff"
has type
  Component
but is expected to have type
  Paint PageToken
in the application
  @Decl.colour PageToken "color" (Component.hash "fff")
-/
#guard_msgs in
example : Decl PageToken := .colour "color" (Component.hash "fff")

-- A token of another kind is no colour: a family where a colour is asked.
/--
error: Application type mismatch: The argument
  PageToken.name
has type
  PageToken Kind.family
but is expected to have type
  PageToken Kind.colour
in the application
  Paint.token PageToken.name
-/
#guard_msgs in
example : Decl PageToken := .colour "color" (.token .name)

-- A token that the page adds to the look is defined from the look: a colour by a paint.
/--
error: Application type mismatch: The argument
  Component.hash "888"
has type
  Component
but is expected to have type
  Paint PageToken
in the application
  Definition.colour PageToken.quiet (Component.hash "888")
-/
#guard_msgs in
example : Definition PageToken := .colour .quiet (Component.hash "888")

-- A custom property is no plain declaration either: it would be a way around the definition.
/--
error: could not synthesize default value for parameter 'free' using tactics
---
error: Tactic `decide` proved that the proposition
  carries "--quiet" = false
is false
-/
#guard_msgs in
example : Decl PageToken := .plain "--quiet" [.hash "888"]

-- What the lists do not hold is plain, and takes any value: the claim is of the properties of
-- `carries`, and `text-decoration` is not one.
example : Decl PageToken := .plain "text-decoration" [.ident "red"]

-- What the laws of a selector do not give. A selector whose names are plain is writable, and
-- the parser's premise asks more: a type selector whose name starts with two hyphen-minus,
-- before a state, reads as a custom property, and the parser returns no rule for it.
#guard Value.writable (Where.selector (.here (.named "--x")) { state := some "hover" })
#guard !Rule.readable false
  (Css.Rule.style (Where.selector (.here (.named "--x")) { state := some "hover" }) [])
#guard (parseStylesheetText (Rule.text
  (Css.Rule.style (Where.selector (.here (.named "--x")) { state := some "hover" }) []))).rules.length == 0

end WhatwgTest.Html.PageSheet
