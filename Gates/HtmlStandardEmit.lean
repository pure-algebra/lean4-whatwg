import Gates.HtmlStandard

/-!
# Gates.HtmlStandardEmit

The content model of `Whatwg.Html`, generated from the HTML Standard's own
element definitions (slice H6.1 of `docs/HTML-PACKAGE-PLAN.md`, ruling
HP-12). The input is the projection of `Gates.HtmlStandard`: for every
element the standard defines at the pin, its categories and its
content-model sentence as text, with the span digest of its definition
block. The outputs, all drift-checked by `lake exe htmlstandard`:

- `Whatwg/Html/Schema/Tags.lean`: the tag universe (the standard's 113
  elements in source order, and text), markup names, and the void set from
  the standard's own list;
- `Whatwg/Html/Schema/Families.lean`: the standard's categories as
  membership functions, the content sets as membership functions, and the
  transparent payload table;
- `Whatwg/Html/Schema/ContentModel.lean`: one row per element with its
  content set, transparency, digest and the reading it was given;
- `Whatwg/Html/Node/Combinators.lean`: one combinator per element and one
  helper per attribute constructor, uniform.

## How a sentence becomes a set

A content-model sentence is read as a `Model`: a base (`flow`,
`phrasing`, `text`, `nothing`, `metadata`, or a list of named elements
with or without the script-supporting elements), tags and categories added,
tags and categories excluded. Twenty-one exact sentences are read
mechanically (`sentenceModel`), which covers the elements whose model is
one of those sentences verbatim. The remaining elements, whose sentences
are conditional or ordered prose, take an *authored* child-level reading
(`readings`), each pinned to the digest of the block it reads, so that a
re-pin that changes the block fails emission until the reading is
re-examined. The readings are the one place interpretation lives, and the
module they are emitted into records each one beside its row.

Descendant restrictions ("but with no header or footer element
descendants") are read at the child level, and ordered models ("A head
element followed by a body element") as membership; both are stated
simplifications of the model, not divergences from anything.

## Transparency and the closure

An element whose sentence begins with `Transparent` takes its content set
from its context, minus what its sentence excludes (`a`: interactive
content and `a`; `audio`, `video`: media elements; `noscript`: `noscript`;
`canvas`: interactive content). What a sentence *adds* as direct children
only (`source` and `track` under `audio` and `video`, `area` under `map`)
is a labelled child (`Whatwg.Html.Node.Evidence.labelledChild`), not part
of any set, and a context's own additions (`figcaption` under `figure`) do
not pass through a transparent element. The content sets are the closure
of every element's own set under those exclusions, two models with the
same members being one set, computed here; that closure is what TyXML's
`_without_` families spelled by hand, and it is complete by construction.
`ContentSet.parent?` records the set each derived set came from.

## Attributes

The attribute universe is the standard's attribute index and event-handler
index, two tables the standard maintains at its end: one `Attr` per
distinct name (dashes as underscores), plus the custom data and ARIA
prefixes and `role`, which the standard defines outside the index. Each
index row's `Value` cell is read as a kind (`kindOf`): a boolean
attribute, a keyword list with or without the empty string and with or
without an open clause, an integer, a non-negative integer, a
floating-point number, a URL, or text; the reading is by the cell's
leading words and its quoted items, and anything else is text. Each
element's attribute set is every global row, every row naming the element
in its `Element(s)` cell, and the extras. The combinators get one helper
per attribute, valueless for a boolean attribute; `html!` validates a
literal value against its row's kind.
-/

namespace Gates.HtmlStandardEmit

open Gates.Common Gates.HtmlStandard

/-! ## Lean spelling -/

def leanKeywords : List String :=
  ["class", "section", "open", "for", "in", "at", "if", "then", "else", "do", "let", "fun",
   "match", "with", "end", "structure", "abbrev", "def", "theorem", "where", "namespace",
   "variable", "import", "instance", "example", "axiom", "by", "have", "show", "from", "mutual",
   "deriving", "private", "protected", "partial", "unsafe", "noncomputable", "inductive",
   "opaque", "macro", "syntax", "attribute", "local", "scoped", "universe", "calc", "suffices",
   "obtain", "exists", "forall", "hiding", "renaming", "using", "extends", "return", "break",
   "continue", "unless", "set_option", "omit", "include", "export", "nomatch", "nofun", "rec",
   "notation", "infix", "prefix", "postfix", "elab", "true", "false", "sorry", "admit", "try",
   "catch", "finally", "throw", "pure", "unfold", "generalizing", "type", "data", "this",
   "meta", "nonrec", "init", "run_cmd", "run_elab", "run_meta"]

/-- The Lean constructor name of a markup name: dashes to underscores,
guillemets when the result is a Lean keyword. -/
def ctorName (name : String) : String :=
  let base := name.replace "-" "_"
  if leanKeywords.contains base then "«" ++ base ++ "»" else base

/-- A set-membership function: constructor dispatch, eight members per line. -/
def emitBoolSet (fn : String) (doc : String) (domain : String) (members : List String) (domainCtors : List String) : String :=
  let members := domainCtors.filter members.contains
  if members.isEmpty then
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool := fun _ => false\n\n"
  else if members.length == domainCtors.length then
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool := fun _ => true\n\n"
  else
    let chunks := Id.run do
      let mut lines : List String := []
      let mut cur : List String := []
      for m in members do
        cur := cur ++ ["." ++ ctorName m]
        if cur.length == 8 then
          lines := lines ++ [String.intercalate " | " cur]
          cur := []
      if !cur.isEmpty then lines := lines ++ [String.intercalate " | " cur]
      lines
    let alts := String.intercalate "\n  | " chunks
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool\n  | {alts} => true\n  | _ => false\n\n"

def emitEnum (name : String) (doc : String) (ctors : List String) : String :=
  let lines := Id.run do
    let mut out : List String := []
    let mut cur : List String := []
    for c in ctors do
      cur := cur ++ [ctorName c]
      if cur.length == 8 then
        out := out ++ ["  | " ++ String.intercalate " | " cur]
        cur := []
    if !cur.isEmpty then out := out ++ ["  | " ++ String.intercalate " | " cur]
    out
  s!"/-- {doc} -/\ninductive {name} where\n{String.intercalate "\n" lines}\n  deriving DecidableEq, Repr, Inhabited\n\n"

def emitStringFn (fn : String) (doc : String) (domain : String) (rows : List (String × String)) : String :=
  let alts := rows.map fun (c, s) => s!"  | .{ctorName c} => \"{s}\""
  s!"/-- {doc} -/\ndef {fn} : {domain} → String\n{String.intercalate "\n" alts}\n\n"

def emitAll (fn : String) (doc : String) (domain : String) (ctors : List String) : String :=
  let items := ctors.map fun c => "." ++ ctorName c
  let lines := Id.run do
    let mut out : List String := []
    let mut cur : List String := []
    for i in items do
      cur := cur ++ [i]
      if cur.length == 8 then
        out := out ++ ["   " ++ String.intercalate ", " cur ++ ","]
        cur := []
    if !cur.isEmpty then out := out ++ ["   " ++ String.intercalate ", " cur]
    out
  let body := String.intercalate "\n" lines
  let body := if body.endsWith "," then dropLastChars body 1 else body
  s!"/-- {doc} -/\ndef {fn} : List {domain} :=\n  [{dropChars body 3}]\n\n"

/-! ## Categories -/

def catFlow := "Flow content."
def catPhrasing := "Phrasing content."
def catHeading := "Heading content."
def catSectioning := "Sectioning content."
def catInteractive := "Interactive content."
def catMetadata := "Metadata content."
def catEmbedded := "Embedded content."
def catPalpable := "Palpable content."
def catScriptSupporting := "Script-supporting element."

/-- The standard's media elements. -/
def mediaElements : List String := ["audio", "video"]

/-- The text pseudo-tag. -/
def textTag : String := "pcdata"

/-- A row lists the category unconditionally, or under a condition (read
conservatively as listed: a typed model does not see attributes). -/
def hasCat (r : Row) (cat : String) : Bool :=
  r.categories.any fun c => c == cat || (c.splitOn (": " ++ cat)).length > 1 || (c.splitOn (": " ++ cat.decapitalize)).length > 1

/-- Category membership by name, over the projection. -/
def catOf (rows : List Row) (cat : String) (tag : String) : Bool :=
  match rows.find? (·.name == tag) with
  | some r => hasCat r cat
  | none => false

/-! ## Models -/

inductive Base where
  | flow | phrasing | text | nothing | metadata
  | only (names : List String) (scriptSupporting : Bool)
  deriving BEq, Repr, Inhabited

structure Model where
  base : Base
  plusTags : List String := []
  plusCats : List String := []
  minusTags : List String := []
  minusCats : List String := []
  deriving BEq, Repr, Inhabited

def sortStrings (xs : List String) : List String :=
  (xs.eraseDups.toArray.qsort (· < ·)).toList

def Model.normalize (m : Model) : Model :=
  { m with plusTags := sortStrings m.plusTags, plusCats := sortStrings m.plusCats,
           minusTags := sortStrings m.minusTags, minusCats := sortStrings m.minusCats }

/-- Drop an excluded tag that an excluded category already excludes (`a`
under `interactive content`), so that the name says no more than the
membership does. -/
def Model.simplify (rows : List Row) (m : Model) : Model :=
  let covered (t : String) : Bool := m.minusCats.any fun c =>
    if c == "media" then mediaElements.contains t else catOf rows c t
  { m with minusTags := m.minusTags.filter fun t => !covered t }.normalize

def Base.name : Base → String
  | .flow => "flow" | .phrasing => "phrasing" | .text => "text" | .nothing => "nothing"
  | .metadata => "metadata"
  | .only names ss => "only_" ++ "_".intercalate names ++ (if ss then "" else "_strict")

def catShort (cat : String) : String :=
  match cat with
  | "Interactive content." => "interactive" | "Heading content." => "heading"
  | "Sectioning content." => "sectioning" | "media" => "media" | c => c

def Model.name (m : Model) : String :=
  m.base.name ++
  (if m.plusCats.isEmpty && m.plusTags.isEmpty then "" else
    "_with_" ++ "_".intercalate (m.plusCats.map catShort ++ m.plusTags)) ++
  (if m.minusCats.isEmpty && m.minusTags.isEmpty then "" else
    "_without_" ++ "_".intercalate (m.minusCats.map catShort ++ m.minusTags))

/-- Membership of a tag in a model, over the projection's categories. -/
def Model.admits (rows : List Row) (m : Model) (tag : String) : Bool :=
  let cat (c : String) : Bool :=
    if c == "media" then mediaElements.contains tag else catOf rows c tag
  let isText := tag == textTag
  let base := match m.base with
    | .flow => isText || cat catFlow
    | .phrasing => isText || cat catPhrasing
    | .text => isText
    | .nothing => false
    | .metadata => cat catMetadata
    | .only names ss => names.contains tag || (ss && (tag == "script" || tag == "template"))
  let plus := m.plusTags.contains tag || m.plusCats.any cat
  (base || plus) && !m.minusTags.contains tag && !m.minusCats.any cat

/-- The twenty-one sentences read mechanically. -/
def sentenceModel : List String → Option Model
  | ["Phrasing content."] => some { base := .phrasing }
  | ["Flow content."] => some { base := .flow }
  | ["Nothing."] => some { base := .nothing }
  | ["Nothing (for clarification, see example)."] => none
  | ["Text."] => some { base := .text }
  | ["Text that is not inter-element whitespace."] => some { base := .text }
  | ["Text that gives a conformant style sheet."] => some { base := .text }
  | ["Zero or more tr and script-supporting elements."] => some { base := .only ["tr"] true }
  | ["Zero or more li and script-supporting elements."] => some { base := .only ["li"] true }
  | ["Zero or more td, th, and script-supporting elements."] => some { base := .only ["td", "th"] true }
  | ["Flow content, but with no header or footer element descendants."] =>
      some { base := .flow, minusTags := ["footer", "header"] }
  | ["Flow content, but with no header, footer, sectioning content, or heading content descendants."] =>
      some { base := .flow, minusTags := ["footer", "header"], minusCats := [catSectioning, catHeading] }
  | ["Flow content, but with no heading content descendants, no sectioning content descendants, and no header, footer, or address element descendants."] =>
      some { base := .flow, minusTags := ["address", "footer", "header"], minusCats := [catSectioning, catHeading] }
  | ["Flow content, but with no form element descendants."] => some { base := .flow, minusTags := ["form"] }
  | ["Flow content, but with no descendant table elements."] => some { base := .flow, minusTags := ["table"] }
  | ["Phrasing content, but there must be no dfn element descendants."] => some { base := .phrasing, minusTags := ["dfn"] }
  | ["Phrasing content, but there must be no progress element descendants."] => some { base := .phrasing, minusTags := ["progress"] }
  | ["Phrasing content, but there must be no meter element descendants."] => some { base := .phrasing, minusTags := ["meter"] }
  | ["Phrasing content, optionally intermixed with heading content."] => some { base := .phrasing, plusCats := [catHeading] }
  | _ => none

/-- A transparent element: what it removes from and adds to its context. -/
structure Transparent where
  name : String
  minusTags : List String := []
  minusCats : List String := []
  deriving Repr, Inhabited

/-- The transparent elements and their exclusions, from their sentences. -/
def transparents : List Transparent :=
  [{ name := "a", minusTags := ["a"], minusCats := [catInteractive] },
   { name := "ins" }, { name := "del" }, { name := "object" }, { name := "slot" },
   { name := "map" },
   { name := "canvas", minusCats := [catInteractive] },
   { name := "audio", minusCats := ["media"] },
   { name := "video", minusCats := ["media"] },
   { name := "noscript", minusTags := ["noscript"] }]

/-- An authored child-level reading of a sentence this generator does not
read mechanically, pinned to the digest of the block it reads. -/
structure Reading where
  name : String
  digest : String
  model : Model
  note : String
  deriving Repr, Inhabited

def readings : List Reading :=
  [{ name := "html", digest := "d750901ea4cfb34e89bd18c4329ef5ca1a68a631913a4a507035aa1120fa9d70",
     model := { base := .only ["head", "body"] false }, note := "\"A head element followed by a body element.\": the two, order not enforced" },
   { name := "head", digest := "faa39dd2013b03e002218eb818f5e348249adb7d2229a5cab975f20618222a6a",
     model := { base := .metadata }, note := "metadata content; the one-title and at-most-one-base bounds are not enforced" },
   { name := "hgroup", digest := "7aa278b8f2ea0c9db066537a70b1696bf73217f0f5065d509bcca35cb958716d",
     model := { base := .only ["p", "h1", "h2", "h3", "h4", "h5", "h6"] true }, note := "\"Zero or more p elements, followed by one h1..h6 element, followed by zero or more p elements\": membership, order not enforced" },
   { name := "dl", digest := "4038905c1cfb9c4fdedabd2fba6820cc7b121efc5d27a249d82ea2bacd85154c", model := { base := .only ["dt", "dd", "div"] true }, note := "dt/dd groups or div wrappers: membership, grouping not enforced" },
   { name := "figure", digest := "623700751d997a7e952558f4c71397c41d4fe50b71c7770cabc01c4b623ddae6", model := { base := .flow, plusTags := ["figcaption"] }, note := "flow content with one figcaption first or last: the count and position are not enforced" },
   { name := "div", digest := "4ab24ed390f90916468b62af3182f12e331da180b1803af35e66bd70546096c2", model := { base := .flow }, note := "flow content; the dt/dd case of a div inside dl is not admitted (the stricter side)" },
   { name := "ruby", digest := "38a3b8701b38542d393c27fa9a73dc46e5e697b4553ab41ee461164fef93a3e6", model := { base := .phrasing, plusTags := ["rt", "rp"] }, note := "\"See prose.\": phrasing with rt and rp annotations, order not enforced" },
   { name := "time", digest := "cb8a2f7a8cf252a847c6f611d9bd4e31f842e23a8796ce7557330f5f438ecb03", model := { base := .phrasing }, note := "phrasing content when datetime is present; the attribute is not seen" },
   { name := "picture", digest := "b2ba70e3ad690bf0dd72fe109abf4e97d3105e0b00b561ad80d6bae8b7ff5022", model := { base := .only ["source", "img"] true }, note := "sources then one img: membership, the count and order are not enforced" },
   { name := "table", digest := "7281e376185588441f7c35a87b2c817c2c681688caa31a6aaf288c590e50390c", model := { base := .only ["caption", "colgroup", "thead", "tbody", "tfoot", "tr"] true }, note := "\"In this order: ...\": membership, order and the tbody-or-tr choice not enforced" },
   { name := "colgroup", digest := "c529973ec5d53cfa7e031bda87dc827c56f32863f97904046905775c308b107d", model := { base := .only ["col", "template"] false }, note := "col and template when span is absent; the attribute is not seen" },
   { name := "label", digest := "b2f05b54776d0ee82a52278d7e4dab759112cdea6f238d4cf2ac650aa3999087", model := { base := .phrasing, minusTags := ["label"] }, note := "phrasing with no label descendants; the labelable-descendant rule is not seen" },
   { name := "button", digest := "aac62eb3d4ff82ce8800119cd9dae55e93365ce280f03d37fac892055cf7e9d6", model := { base := .phrasing, minusCats := [catInteractive] }, note := "phrasing with no interactive content descendant; tabindex is not seen" },
   { name := "select", digest := "fe337946a811fc79b1fed2bf90064f2ee72052cd216a46ac180a2c10f64df393", model := { base := .only ["button", "option", "optgroup", "hr", "noscript"] true }, note := "the customizable-select model: membership, the one-button bound not enforced" },
   { name := "datalist", digest := "424561578425cce06aed8ab0becc70e1a2a4d492e8dda5f337c8b37dc54ecb10", model := { base := .phrasing, plusTags := ["option"] }, note := "\"Either: phrasing content. Or: Zero or more option and script-supporting elements.\": the union" },
   { name := "optgroup", digest := "e3977cee5a08b732a7178474cee97d9941ce99a2c1f83ae5688187ed5a19c738", model := { base := .only ["legend", "option", "noscript", "div"] true }, note := "the customizable-select model: membership" },
   { name := "option", digest := "1375746e60ce3c9e85146c7ab0f95a0c0a1582a4f7acaa1e62dcee2ab5ba1263", model := { base := .text }, note := "text; the label/value cases and the customizable-select div case are not admitted (the stricter side)" },
   { name := "fieldset", digest := "65e8d175a18f7adb66e20cdfca9d158b73a235f662bb38cf4202e1a6a66be5ac", model := { base := .flow, plusTags := ["legend"] }, note := "\"Optionally, a legend element, followed by flow content.\": position not enforced" },
   { name := "legend", digest := "96b445d4e81c4530b9ba5e5fc341d803d62361e806955356b2d9bf04ca0b6c0d", model := { base := .phrasing, plusCats := [catHeading] }, note := "\"Phrasing content, optionally intermixed with heading content.\" outside an optgroup" },
   { name := "details", digest := "dae4636d68540e86cc746b5f565213e110a4cfa1299e50a4acdb21c4e853b9a9", model := { base := .flow, plusTags := ["summary"] }, note := "\"One summary element followed by flow content.\": the count and position are not enforced" },
   { name := "script", digest := "564635dd098ee1924180c4a7cedebb715fe0b4ecb5766522869e11ee7364047c", model := { base := .text }, note := "script content restrictions are prose; text" },
   { name := "template", digest := "66a1966da3e921dcc46fe23ff1b42c9b63ce8f32c47aa630ee06b4356f9fb622", model := { base := .flow }, note := "the DOM children are \"Nothing\" and the template contents are a fragment the HTML syntax writes inside the element; the authoring reading is flow content" },
   { name := "canvas", digest := "d57b26e741d2789236bd9b8e02967d8f2974b1c13dcbb5417639cd44afc2ce1e", model := { base := .flow, minusCats := [catInteractive] }, note := "transparent, with no interactive content descendants; the exceptions for a, img with usemap, button and some inputs are not seen; own set in flow context" },
   { name := "a", digest := "47fe774c5f4df179114fc71a733cdecab8e037191196918924eed477d89cb40e", model := { base := .flow, minusTags := ["a"], minusCats := [catInteractive] }, note := "transparent, with no interactive content or a descendants; own set in flow context" },
   { name := "video", digest := "aebbd45003249b39a1f4fd1a5eb1832215cee9ba7b0609c5b96feb6ce4b32858", model := { base := .flow, minusCats := ["media"] }, note := "transparent with no media element descendants; source and track are labelled direct children; own set in flow context" },
   { name := "audio", digest := "9170b66d7cb774c8a033e021bdbd1edd28383365e6290ae4230273ade3a694ff", model := { base := .flow, minusCats := ["media"] }, note := "as video" },
   { name := "noscript", digest := "8dbcd80015740fb7da22de141aa329b53180e5bd3f17295ba08e3194ac7bf36d", model := { base := .flow, minusTags := ["noscript"] }, note := "transparent with no noscript descendants outside head; in head, link, style and meta (a payload override); own set in flow context" },
   { name := "ins", digest := "59ba25f87f03aeda50ba77b50110d02fa4cd90a4a95193154d8ba7747f3ce5e8", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "del", digest := "957c3085f9a164a6e4aebeb7a3c58463552ecdcda02f17475f00c90b50577ca2", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "object", digest := "5a60e4935a0bd0bf2c39e78e3bf668d9538c9f11a87c64d292ff8fc06e132875", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "slot", digest := "762ea10fa3fcac173bd0a1204ba1538c97f89ee0741a45cb58ac358147bc1899", model := { base := .flow }, note := "transparent; own set in flow context" },
   { name := "map", digest := "ce48cdbf08102b1d3a8a0fef92a8c61dcd574406f27e7755c6180b64830cb165", model := { base := .flow, plusTags := ["area"] }, note := "transparent; area is admitted under a map; own set in flow context" }]

/-- The direct children a sentence admits first and outside any content
set: the parent, the child, and whether the child may repeat. -/
def labelled : List (String × String × Bool) :=
  [("audio", "source", true), ("audio", "track", true), ("video", "source", true), ("video", "track", true),
   ("map", "area", true)]

/-- Payload overrides: a transparent element whose payload in one context
is not the context minus its exclusions. -/
def payloadOverrides : List (String × String × Model) :=
  [("metadata", "noscript", { base := .only ["link", "style", "meta"] false })]

/-! ## Attributes, from the two index tables -/

/-- The kind of an attribute's value, read from the `Value` cell. -/
inductive Kind where
  | boolean | keywords (isOpen : Bool) | integer | nonNegInteger | float | url | text | prefix
  deriving BEq, Repr, Inhabited

def Kind.render : Kind → String
  | .boolean => ".boolean" | .keywords o => s!".keywords {o}" | .integer => ".integer"
  | .nonNegInteger => ".nonNegInteger" | .float => ".float" | .url => ".url" | .text => ".text"
  | .prefix => ".prefix"

/-- The reading of a `Value` cell: the kind, the keywords when it is a
keyword list, and whether the empty string is admitted. -/
def kindOf (value : String) : Kind × List String × Bool :=
  if value.startsWith "Boolean attribute" then (.boolean, [], false)
  else if value.startsWith "\"" then
    let items := (value.splitOn ";").map collapse |>.filter (· != "")
    let quoted := items.filterMap fun i =>
      if i.startsWith "\"" && i.endsWith "\"" && i.length ≥ 2 then some (dropLastChars (dropChars i 1) 1) else none
    let allowEmpty := items.any (· == "the empty string")
    let open_ := items.any fun i => !(i.startsWith "\"") && i != "the empty string"
    (.keywords open_, quoted, allowEmpty)
  else if value.startsWith "Valid non-negative integer" then (.nonNegInteger, [], false)
  else if value.startsWith "Valid integer" then (.integer, [], false)
  else if value.startsWith "Valid floating-point number" then (.float, [], false)
  else if value.startsWith "Valid URL" || value.startsWith "Valid non-empty URL" then (.url, [], false)
  else (.text, [], false)

/-- The elements an `Element(s)` cell names, and whether it says every
HTML element. Parentheticals are dropped (`source (in picture)`), the
list is split on `;` and spaces, and only tokens that are element names
count (`form-associated custom elements` names none). -/
def elementsOf (tags : List String) (cell : String) : List String × Bool :=
  let global := (cell.splitOn "HTML elements").length > 1
  let noParen := String.join ((cell.splitOn "(").map fun piece =>
    match piece.splitOn ")" with | [] => "" | [x] => x | _ :: rest => ")".intercalate rest)
  let tokens := (noParen.replace ";" " ").splitOn " " |>.map collapse |>.filter (· != "")
  (tokens.filter tags.contains |>.eraseDups, global)

/-- Attributes the standard defines outside its index, admitted on every
element: the custom data attributes, and the ARIA `role` and `aria-*`
attributes that `ARIA in HTML` defines. -/
def extraAttrs : List (String × Kind × String) :=
  [("data-", .prefix, "custom data attribute prefix (`data-*`), on every element"),
   ("role", .text, "ARIA role, defined in ARIA in HTML, on every element"),
   ("aria-", .prefix, "ARIA state and property prefix (`aria-*`), on every element")]

structure AttrOut where
  markup : String
  handler : Bool
  elements : List String
  global : Bool
  kind : Kind
  keywords : List String
  allowEmpty : Bool
  description : String
  digest : String
  deriving Repr, Inhabited

def attrOuts (tags : List String) (rows : List AttrRow) : List AttrOut :=
  rows.map fun r =>
    let (els, global) := elementsOf tags r.elements
    let (kind, kws, allowEmpty) := kindOf r.value
    { markup := r.name, handler := r.handler, elements := els, global, kind, keywords := kws, allowEmpty,
      description := r.description, digest := r.digest }

/-- The distinct attribute names, in table order, then the extras. -/
def attrNames (outs : List AttrOut) : List String :=
  (outs.map (·.markup)).eraseDups ++ extraAttrs.map (·.1)

/-- The helper name of an attribute: `a_` and the markup name with dashes
as underscores (`a_accept_charset`, `a_data` for the prefix). -/
def helperName (markup : String) : String :=
  "a_" ++ (if markup.endsWith "-" then dropLastChars markup 1 else markup).replace "-" "_"

/-- The attribute set of an element: every global row, every row naming
it, and the extras. -/
def attrSetOf (outs : List AttrOut) (element : String) : List String :=
  ((outs.filter fun o => o.global || o.elements.contains element).map (·.markup)).eraseDups ++
    extraAttrs.map (·.1)

/-! ## The schema -/

structure Set where
  name : String
  model : Model
  parent : Option String
  deriving Repr, Inhabited

structure ElementOut where
  row : Row
  model : Model
  transparent : Bool
  reading : String
  deriving Repr, Inhabited

structure Schema where
  rows : List Row
  attrs : List AttrOut
  tags : List String
  voidTags : List String
  voidDigest : String
  elements : List ElementOut
  sets : List Set
  payloads : List (String × String × String)
  deriving Repr, Inhabited

/-- Transparent by the authored list `transparents`, which also covers the
elements whose sentence is conditional (`audio`, `video`, `noscript`). -/
def isTransparent (r : Row) : Bool :=
  transparents.any (·.name == r.name)

/-- The model of a row: the mechanical reading, else the authored one. -/
def modelOf (r : Row) : Except String (Model × String) := do
  match readings.find? (·.name == r.name) with
  | some rd =>
    unless rd.digest.isEmpty || rd.digest == r.digest do
      throw s!"html standard emit: the reading of `{r.name}` is pinned to digest {rd.digest} but the block now has {r.digest}; re-examine the reading"
    return (Model.simplify [] rd.model, "authored: " ++ rd.note)
  | none =>
    match sentenceModel r.contentModel with
    | some m => return (m.normalize, "sentence")
    | none => throw s!"html standard emit: no reading for `{r.name}`: {r.contentModel}"

/-- Apply a transparent element's exclusions to a context: the context's
own additions (a `figcaption` under `figure`) do not pass through, since
the standard admits them as direct children only. -/
def applyTransparent (rows : List Row) (ctx : Model) (t : Transparent) : Model :=
  Model.simplify rows <|
  { ctx with plusTags := [], plusCats := [], minusTags := ctx.minusTags ++ t.minusTags,
             minusCats := ctx.minusCats ++ t.minusCats }.normalize

/-- The closure of the element sets under the transparent payloads. Two
models with the same members are one set, named by the first model that
reached it (`a` is interactive, so `_without_interactive_a` is
`_without_interactive`). -/
def closure (rows : List Row) (tags : List String) (seeds : List (String × Model)) (fuel : Nat) :
    List Set × List (String × String × String) := Id.run do
  let membersOf (m : Model) : List String := tags.filter (m.admits rows)
  let mut sets : Array (Set × List String) := #[]
  for (n, m) in seeds do
    let mem := membersOf m
    unless sets.any (·.2 == mem) do sets := sets.push ({ name := n, model := m, parent := none }, mem)
  let mut payloads : Array (String × String × String) := #[]
  let mut i := 0
  let mut budget := fuel
  while i < sets.size && budget > 0 do
    budget := budget - 1
    let (s, _) := sets[i]!
    for t in transparents do
      if s.model.admits rows t.name then
        let p := match payloadOverrides.find? fun (c, n, _) => c == s.name && n == t.name with
          | some (_, _, m) => m.normalize
          | none => applyTransparent rows s.model t
        let mem := membersOf p
        match sets.find? (·.2 == mem) with
        | some (e, _) => payloads := payloads.push (s.name, t.name, e.name)
        | none =>
          let nm := p.name
          sets := sets.push ({ name := nm, model := p, parent := some s.name }, mem)
          payloads := payloads.push (s.name, t.name, nm)
    i := i + 1
  return (sets.toList.map (·.1), payloads.toList)

/-- The void elements, from the standard's own list, with its digest. -/
def voidList (text : String) : Except String (List String × String) := do
  let marker := "<dt><dfn>Void elements</dfn></dt>"
  match text.splitOn marker with
  | [_, after] =>
    let dd := upTo (match after.splitOn "<dd>" with | [] => "" | _ :: r => "<dd>".intercalate r) "</dd>"
    let names := ((dd.splitOn "<code>").drop 1).map fun piece => upTo piece "</code>"
    return (names, Gates.Sha256.hexDigestOfString dd)
  | _ => throw "html standard emit: the void-elements list was not found exactly once"

def build (root : System.FilePath) : IO Schema := do
  let text ← readSource root
  let rows := rowsOf text
  let g ← Gates.HtmlStandard.generate root
  let attrs := attrOuts (rows.map (·.name)) g.attrs
  let lift {α} : Except String α → IO α
    | .ok v => pure v
    | .error e => throw <| IO.userError e
  let (voidTags, voidDigest) ← lift (voidList text)
  let mut elements : Array ElementOut := #[]
  for r in rows do
    let (m, reading) ← lift (modelOf r)
    elements := elements.push { row := r, model := Model.simplify rows m, transparent := isTransparent r, reading }
  let seeds := [("flow", ({ base := .flow } : Model)), ("phrasing", { base := .phrasing }),
    ("metadata", { base := .metadata }), ("text", { base := .text }), ("nothing", { base := .nothing })] ++
    elements.toList.map fun e => (e.model.name, e.model)
  let tags := rows.map (·.name) ++ [textTag]
  let (sets, payloads) := closure rows tags seeds 10000
  return { rows, attrs, tags := rows.map (·.name) ++ [textTag], voidTags, voidDigest,
           elements := elements.toList, sets, payloads }

/-! ## Emission -/

def header (moduleName : String) (summary : String) (imports : List String := []) : String :=
  String.join (imports.map fun m => s!"import {m}\n") ++ (if imports.isEmpty then "" else "\n") ++
  s!"/-!\n# {moduleName}\n\n{summary}\n\n" ++
  "GENERATED by `lake exe htmlstandard --write` from the sealed HTML Standard\n" ++
  s!"`{source.relative}` (SHA-256 `{source.digest}`), through the projection\n" ++
  "`generated/html-standard-elements.tsv` and the readings of\n" ++
  "`Gates/HtmlStandardEmit.lean`. DO NOT EDIT: `lake exe htmlstandard` fails on\n" ++
  "any byte of drift. Slice H6.1 of `docs/HTML-PACKAGE-PLAN.md`, ruling HP-12.\n" ++
  "Data and derived instances only: no proof lives here.\n-/\n\n"

def setName (s : Schema) (m : Model) : String :=
  let mem := s.tags.filter (m.admits s.rows)
  match s.sets.find? fun e => s.tags.filter (e.model.admits s.rows) == mem with
  | some e => e.name
  | none => m.name

def emitTags (s : Schema) : String :=
  header "Whatwg.Html.Schema.Tags"
    "The element-tag universe: every element the HTML Standard defines at the\npin, in the order of `source`, and `pcdata`, the text pseudo-tag." ++
  "namespace Whatwg.Html.Schema\n\n" ++
  emitEnum "Tag" "An element tag of the standard, or text." s.tags ++
  emitAll "Tag.all" "Every tag, in source order." "Tag" s.tags ++
  emitStringFn "Tag.variantName" "The tag's name: its markup name, or `pcdata` for text." "Tag" (s.tags.map fun t => (t, t)) ++
  "/-- The markup name of an element tag; `none` for text. -/\ndef Tag.markupName : Tag → Option String\n" ++
  "\n".intercalate (s.rows.map fun r => s!"  | .{ctorName r.name} => some \"{r.name}\"") ++ "\n  | _ => none\n\n" ++
  emitBoolSet "Tag.isVoid"
    (s!"The void elements, from the standard's own list (`Void elements` in the\nsyntax section, span digest `{s.voidDigest}`).") "Tag" s.voidTags s.tags ++
  "end Whatwg.Html.Schema\n"

def emitFamilies (s : Schema) : String := Id.run do
  let names := s.sets.map (·.name)
  let mut out := header "Whatwg.Html.Schema.Families"
    "The standard's categories as membership functions, the content sets (the\nclosure of every element's set under the transparent payloads) as\nmembership functions, the payload table, and the derivation parent of\neach derived set."
    ["Whatwg.Html.Schema.Tags"]
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  for (fn, cat, doc) in [("Cats.flow", catFlow, "Flow content"), ("Cats.phrasing", catPhrasing, "Phrasing content"),
      ("Cats.heading", catHeading, "Heading content"), ("Cats.sectioning", catSectioning, "Sectioning content"),
      ("Cats.interactive", catInteractive, "Interactive content, with the conditional cases read as interactive"),
      ("Cats.metadata", catMetadata, "Metadata content"), ("Cats.embedded", catEmbedded, "Embedded content"),
      ("Cats.palpable", catPalpable, "Palpable content, with the conditional cases read as palpable"),
      ("Cats.scriptSupporting", catScriptSupporting, "Script-supporting elements")] do
    out := out ++ emitBoolSet fn (doc ++ ", by the `Categories` entries of the projection.") "Tag"
      (s.rows.filter (hasCat · cat) |>.map (·.name)) s.tags
  out := out ++ emitBoolSet "Cats.media" "The media elements, `audio` and `video`." "Tag" mediaElements s.tags
  out := out ++ emitEnum "ContentSet" "A content set, by its derived name." names
  out := out ++ emitAll "ContentSet.all" "Every content set, in derivation order." "ContentSet" names
  out := out ++ emitStringFn "ContentSet.name" "The set's name." "ContentSet" (names.map fun n => (n, n))
  for e in s.sets do
    let members := s.tags.filter (e.model.admits s.rows)
    out := out ++ emitBoolSet s!"Sets.{e.name}" s!"`{e.name}`: {members.length} of {s.tags.length} tags." "Tag" members s.tags
  out := out ++ "/-- Membership, dispatching to the set's own function. -/\ndef ContentSet.contains : ContentSet → Tag → Bool\n" ++
    "\n".intercalate (names.map fun n => s!"  | .{ctorName n}, t => Sets.{n} t") ++ "\n\n"
  for e in s.sets do
    let rows := (s.payloads.filter fun (c, _, _) => c == e.name).map fun (_, t, p) => s!"  | .{ctorName t} => some .{ctorName p}"
    out := out ++ s!"/-- The transparent payloads of `{e.name}`: {rows.length} of {s.tags.length} tags carry one. -/\ndef Payloads.{e.name} : Tag → Option ContentSet\n" ++
      "\n".intercalate rows ++ (if rows.isEmpty then "" else "\n") ++ "  | _ => none\n\n"
  out := out ++ "/-- The transparent rule: the content set a transparent element's children\nare checked against when it appears in the given set (the set minus what\nthe element excludes, plus what it adds). `none` when the set does not\nname the tag. Dispatches per set. -/\ndef ContentSet.transparentPayload : ContentSet → Tag → Option ContentSet\n" ++
    "\n".intercalate (names.map fun n => s!"  | .{ctorName n}, t => Payloads.{n} t") ++ "\n\n"
  out := out ++ "/-- The set a derived set was derived from by a transparent payload;\n`none` for an element's own set. -/\ndef ContentSet.parent? : ContentSet → Option ContentSet\n" ++
    "\n".intercalate (s.sets.filterMap fun e => e.parent.map fun p => s!"  | .{ctorName e.name} => some .{ctorName p}") ++ "\n  | _ => none\n\n"
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

def emitAttributes (s : Schema) : String := Id.run do
  let names := attrNames s.attrs
  let mut out := header "Whatwg.Html.Schema.Attributes"
    "The attribute universe of the HTML Standard at the pin: every attribute\nof its attribute index and event-handler index, the custom data and ARIA\nprefixes, the reading of each index row's `Value` cell as a kind, one\nattribute set per element from the `Element(s)` cells, and one helper row\nper attribute for the combinators."
    ["Whatwg.Html.Schema.Tags"]
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  out := out ++ emitEnum "Attr" "An attribute of the standard, by markup name (dashes as underscores); the two prefixes end in `_`." names
  out := out ++ emitAll "Attr.all" "Every attribute, in index order, then the extras." "Attr" names
  out := out ++ emitStringFn "Attr.markupName" "The markup name of the attribute (the prefix itself for `data_` and `aria_`)." "Attr" (names.map fun n => (n, n))
  out := out ++ "/-- The kind of an attribute's value, read from the index's `Value` cell:\na boolean attribute; a keyword list (`open` when the cell also admits\nvalues the list does not spell); an integer; a non-negative integer; a\nfloating-point number; a URL; text; or a prefix. -/\ninductive AttrValueKind where\n  | boolean | keywords (isOpen : Bool) | integer | nonNegInteger | float | url | text | prefix\n  deriving DecidableEq, Repr, Inhabited\n\n"
  out := out ++ "/-- One row of the attribute index: the attribute, the elements it applies\nto (`global` when the cell says every HTML element), the value kind, the\nkeywords and whether the empty string is admitted, the description, and\nthe span digest of the row. -/\nstructure AttrRow where\n  attr : Attr\n  markup : String\n  handler : Bool\n  elements : List Tag\n  global : Bool\n  kind : AttrValueKind\n  keywords : List String\n  allowEmpty : Bool\n  description : String\n  digest : String\n  deriving Repr, Inhabited\n\n"
  let rowText (o : AttrOut) : String :=
    "   { attr := ." ++ ctorName o.markup ++ ", markup := " ++ o.markup.quote ++ ", handler := " ++ toString o.handler ++
    ", elements := [" ++ ", ".intercalate (o.elements.map fun e => "." ++ ctorName e) ++ "], global := " ++ toString o.global ++
    ",\n     kind := " ++ o.kind.render ++ ", keywords := [" ++ ", ".intercalate (o.keywords.map String.quote) ++ "], allowEmpty := " ++ toString o.allowEmpty ++
    ",\n     description := " ++ o.description.quote ++ ",\n     digest := " ++ o.digest.quote ++ " }"
  let extraRows := extraAttrs.map fun (m, k, d) =>
    "   { attr := ." ++ ctorName m ++ ", markup := " ++ m.quote ++ ", handler := false, elements := [], global := true,\n     kind := " ++ k.render ++ ", keywords := [], allowEmpty := false,\n     description := " ++ d.quote ++ ",\n     digest := \"\" }"
  out := out ++ "/-- Every row of the two indexes, then the extras (whose digest is empty:\nthey are not index rows). -/\ndef attributeRows : List AttrRow :=\n  [" ++
    dropChars (",\n".intercalate (s.attrs.map rowText ++ extraRows)) 3 ++ "]\n\n"
  out := out ++ "/-- One helper per attribute for `Whatwg.Html.A`: the helper's name, the\nattribute, and the kind that fixes the helper's shape (a boolean attribute\ntakes no value; a prefix has no helper). -/\nstructure AttrCtor where\n  name : String\n  markup : String\n  isPrefix : Bool\n  tag : Attr\n  kind : AttrValueKind\n  deriving Repr, Inhabited\n\n"
  let kindFor (n : String) : Kind :=
    match extraAttrs.find? (fun (e : String × Kind × String) => e.1 == n) with
    | some (_, k, _) => k
    | none => match s.attrs.find? (·.markup == n) with
      | some o => if s.attrs.all (fun p => p.markup != n || p.kind == .boolean) then o.kind else
          (if o.kind == .boolean then .text else o.kind)
      | none => .text
  out := out ++ "/-- Every helper, in `Attr.all` order. -/\ndef attributeCtors : List AttrCtor :=\n  [" ++
    dropChars (",\n".intercalate (names.map fun n =>
      "   { name := " ++ (helperName n).quote ++ ", markup := " ++ n.quote ++ ", isPrefix := " ++ toString (n.endsWith "-") ++
      ", tag := ." ++ ctorName n ++ ", kind := " ++ (kindFor n).render ++ " }")) 3 ++ "]\n\n"
  let setNames := s.rows.map fun r => r.name ++ "_attrib"
  out := out ++ emitEnum "AttrSet" "The attribute set of an element, by element name." setNames
  out := out ++ emitAll "AttrSet.all" "Every attribute set, in source order." "AttrSet" setNames
  out := out ++ emitStringFn "AttrSet.name" "The set's name." "AttrSet" (setNames.map fun n => (n, n))
  for r in s.rows do
    let members := attrSetOf s.attrs r.name
    out := out ++ emitBoolSet s!"AttrSets.{r.name}_attrib" s!"The attributes of `{r.name}`: {members.length} of {names.length}." "Attr" members names
  out := out ++ "/-- Membership, dispatching to the set's own function. -/\ndef AttrSet.contains : AttrSet → Attr → Bool\n" ++
    "\n".intercalate (setNames.map fun n => s!"  | .{ctorName n}, a => AttrSets.{n} a") ++ "\n\n"
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

def emitContentModel (s : Schema) : String :=
  let rows := s.elements.map fun e =>
    "   { name := \"" ++ e.row.name ++ "\", tag := ." ++ ctorName e.row.name ++ ", kind := ." ++
      (if s.voidTags.contains e.row.name || e.model.base == .nothing then "nullary" else "star") ++
      ", transparent := " ++ toString e.transparent ++ ", content := ." ++ ctorName (setName s e.model) ++
      ", attribs := ." ++ ctorName (e.row.name ++ "_attrib") ++ ",\n     digest := \"" ++ e.row.digest ++ "\", reading := " ++ e.reading.quote ++ " }"
  header "Whatwg.Html.Schema.ContentModel"
    "One row per element of the standard: its tag, whether it takes children,\nwhether it is transparent, its content set (a transparent element's own\nset is its payload in flow context), its attribute set, the span digest of\nits definition, and the reading its sentence was given: `sentence` when\nread mechanically, `authored: ...` otherwise."
    ["Whatwg.Html.Schema.Tags", "Whatwg.Html.Schema.Families", "Whatwg.Html.Schema.Attributes"] ++
  "namespace Whatwg.Html.Schema\n\n" ++
  "/-- Whether an element takes children. -/\ninductive ElementKind where\n  | star | nullary\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
  "/-- One element of the standard. -/\nstructure Element where\n  name : String\n  tag : Tag\n  kind : ElementKind\n  transparent : Bool\n  content : ContentSet\n  attribs : AttrSet\n  digest : String\n  reading : String\n  deriving Repr, Inhabited\n\n" ++
  "/-- Every element, in source order. -/\ndef elements : List Element :=\n  [" ++ dropChars (",\n".intercalate rows) 3 ++ "]\n\n" ++
  "/-- The position in `elements` of a tag; `none` for text. -/\ndef Tag.elementIndex? : Tag → Option Nat\n" ++
  "\n".intercalate (s.elements.zipIdx.map fun (e, i) => s!"  | .{ctorName e.row.name} => some {i}") ++ "\n  | _ => none\n\n" ++
  "/-- The element of a tag. -/\ndef Tag.element? (t : Tag) : Option Element :=\n  t.elementIndex?.bind (elements[·]?)\n\n" ++
  "/-- The direct children a sentence admits first and outside any content set\n(`source` and `track` under `audio` and `video`, `area` under `map`). -/\ndef labelledChild : Tag → Tag → Bool\n" ++
  "\n".intercalate (labelled.map fun (p, c, _) => s!"  | .{ctorName p}, .{ctorName c} => true") ++ "\n  | _, _ => false\n\n" ++
  "/-- The content set of a tag, as one flat match: `none` for text. It denotes\n`(Tag.element? t).map Element.content` (`Whatwg.Html.Content.content?_eq_element?`)\nand exists because the child-set resolver is reduced at every node. -/\ndef Tag.content? : Tag → Option ContentSet\n" ++
  "\n".intercalate (s.elements.map fun e => s!"  | .{ctorName e.row.name} => some .{ctorName (setName s e.model)}") ++ "\n  | _ => none\n\n" ++
  "end Whatwg.Html.Schema\n"

def emitCombinators (s : Schema) : String := Id.run do
  let mut out := "import Whatwg.Html.Node.Typed\nimport Whatwg.Html.Node.Admit\n\n/-!\n# Whatwg.Html.Node.Combinators\n\nOne combinator per element of the standard, in source order, the two text\nconstructors, `el`, and one helper per attribute of the standard. Every combinator has the same shape: children first, then\n`attrs` with a default of `[]`, then the attribute obligation `_ha`\ndischarged by the `admits` tactic; a void or childless element has no\nchildren parameter; a transparent element is polymorphic in its content\nset, which `Child.of` assigns from the position it is placed in (ruling\nHP-4). The names live in `Whatwg.Html.E` and `Whatwg.Html.A` because a\ndozen are single letters. `audio`, `video` and `map` take their labelled\ndirect children (`sources`, `tracks`, `areas`) as lists placed first.\n\n" ++
    "GENERATED by `lake exe htmlstandard --write` (see `Gates/HtmlStandardEmit.lean`).\nDO NOT EDIT: `lake exe htmlstandard` fails on any byte of drift.\n-/\n\nnamespace Whatwg.Html.E\n\nopen Whatwg.Html.Schema (Tag ContentSet Attr AttrSet)\n\n" ++
    "/-- A text run, admitted where the content set names text. -/\ndef txt {set : ContentSet} (s : String)\n    (h : Content.Admits set .pcdata := by admits) : Child set :=\n  Child.text s h\n\n" ++
    "/-- A named entity reference, admitted where text is. -/\ndef entity {set : ContentSet} (name : String)\n    (h : Content.Admits set .pcdata := by admits) : Child set :=\n  Child.entity name h\n\n" ++
    "/-- Place a typed element in a child position: `Child.of` under a short name. -/\ndef el {set : ContentSet} {t : Tag} (e : Element t (childSet set t))\n    (h : Content.Admits set t := by admits) : Child set :=\n  Child.of e h\n\n"
  for e in s.elements do
    let n := ctorName e.row.name
    let tag := "." ++ n
    let content := "." ++ ctorName (setName s e.model)
    let nullary := s.voidTags.contains e.row.name || e.model.base == .nothing
    let attrs := s!"    (attrs : List (Attr × String) := [])\n    (_ha : AttrsAdmitted .{ctorName (e.row.name ++ "_attrib")} attrs := by admits) :\n"
    let doc := s!"/-- `{e.row.name}`: {e.reading}. -/\n"
    let labs := (labelled.filter fun (p, _, _) => p == e.row.name).map (·.2.1)
    let labParams := String.join (labs.map fun c =>
      s!"    ({c}s : List (Element .{ctorName c} .nothing) := [])\n")
    let labRaw := String.join (labs.map fun c => s!"{c}s.map Element.toRaw ++ ")
    let laParams := ""
    let laAttrs := ""
    if nullary then
      out := out ++ doc ++ s!"def {n} {laParams}\n" ++ attrs ++ s!"    Element {tag} {content} :=\n  ⟨{laAttrs}attrs, []⟩\n\n"
    else if e.transparent then
      out := out ++ doc ++ s!"def {n} " ++ "{inner : ContentSet} " ++ laParams ++ "(children : List (Child inner) := [])\n" ++ labParams ++ attrs ++
        s!"    Element {tag} inner :=\n  ⟨{laAttrs}attrs, {labRaw}children.map Child.raw⟩\n\n"
    else
      out := out ++ doc ++ s!"def {n} {laParams}(children : List (Child {content}) := [])\n" ++ labParams ++ attrs ++
        s!"    Element {tag} {content} :=\n  ⟨{laAttrs}attrs, {labRaw}children.map Child.raw⟩\n\n"
  out := out ++ "end Whatwg.Html.E\n\nnamespace Whatwg.Html.A\n\nopen Whatwg.Html.Schema (Attr)\n\n"
  let names := attrNames s.attrs
  for n in names do
    if n.endsWith "-" then continue
    let boolean : Bool := match extraAttrs.find? (fun (e : String × Kind × String) => e.1 == n) with
      | some _ => false
      | none => s.attrs.all fun p => p.markup != n || p.kind == .boolean
    let desc : String := match s.attrs.find? (·.markup == n) with
      | some o => o.description
      | none => match extraAttrs.find? (fun (e : String × Kind × String) => e.1 == n) with
        | some (_, _, d) => d
        | none => ""
    if boolean then
      out := out ++ s!"/-- `{n}`: {desc}. A boolean attribute: present, with the empty string as its value. -/\ndef {helperName n} : Attr × String := (.{ctorName n}, \"\")\n\n"
    else
      out := out ++ s!"/-- `{n}`: {desc}. -/\ndef {helperName n} (value : String) : Attr × String := (.{ctorName n}, value)\n\n"
  out := out ++ "end Whatwg.Html.A\n"
  return out

def modulePaths : List String :=
  ["Whatwg/Html/Schema/Tags.lean", "Whatwg/Html/Schema/Families.lean", "Whatwg/Html/Schema/Attributes.lean",
   "Whatwg/Html/Schema/ContentModel.lean", "Whatwg/Html/Node/Combinators.lean"]

structure Emitted where
  schema : Schema
  files : List (String × String)

def emitModules (root : System.FilePath) : IO Emitted := do
  let s ← build root
  return { schema := s, files := modulePaths.zip [emitTags s, emitFamilies s, emitAttributes s, emitContentModel s, emitCombinators s] }

def summarize (s : Schema) : String :=
  let authored := (s.elements.filter fun e => e.reading.startsWith "authored").length
  s!"html standard emit: {s.rows.length} elements ({s.rows.length - authored} read from their sentence, {authored} authored readings), " ++
  s!"{s.sets.length} content sets, {s.payloads.length} payload rows, {s.voidTags.length} void tags, " ++
  s!"{(attrNames s.attrs).length} attributes from {s.attrs.length} index rows, {s.rows.length} attribute sets\n"

/-- Write the modules; called by `Gates.HtmlStandard` after the projection. -/
def write (root : System.FilePath) : IO UInt32 := do
  let e ← emitModules root
  for (path, text) in e.files do
    IO.FS.writeFile (root / path) text
    IO.println s!"WROTE {path}"
  IO.print (summarize e.schema)
  return 0

/-- Check every module for drift. -/
def check (root : System.FilePath) : IO (List String) := do
  let e ← emitModules root
  let mut failures : List String := []
  for (path, fresh) in e.files do
    let p := root / path
    unless ← p.pathExists do
      failures := failures ++ [s!"missing generated module {path}; run `lake exe htmlstandard --write`"]
      continue
    let committed ← IO.FS.readFile p
    if committed != fresh then
      let expected := lines fresh
      let actual := lines committed
      failures := failures ++ [s!"module drift in {path} ({actual.length} committed lines, {expected.length} regenerated)"]
      let mut shown := 0
      for (x, a) in expected.zip actual do
        if x != a && shown < 10 then
          failures := failures ++ [s!"  regenerated: {x}", s!"  committed:   {a}"]
          shown := shown + 1
  IO.print (summarize e.schema)
  return failures

def usage : String :=
  "usage: lake exe htmlstandard          check the two projections, the data module and the five generated modules against a regeneration\n" ++
  "       lake exe htmlstandard --write  regenerate all of them from the sealed HTML Standard source"

/-- Command-line entry, invoked by `bin/HtmlStandard.lean`: the projection
gate of `Gates.HtmlStandard` first, then the schema modules. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] =>
    let rc ← Gates.HtmlStandard.check root
    if rc != 0 then return rc
    let failures ← check root
    if failures.isEmpty then
      IO.println "PASS html standard emit: the five generated schema modules are byte-identical to a fresh emission"
      return 0
    for f in failures do IO.eprintln f
    IO.eprintln "FAIL html standard emit"
    return 1
  | ["--write"] =>
    let rc ← Gates.HtmlStandard.write root
    if rc != 0 then return rc
    write root
  | _ =>
    IO.eprintln usage
    return 2

end Gates.HtmlStandardEmit
