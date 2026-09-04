import Gates.HtmlStandard
import Whatwg.Html.Schema.Readings

/-!
# Gates.HtmlStandardEmit

The content model of `Whatwg.Html`, generated from the HTML Standard's own
element definitions and attribute indexes (slices H6.1 and H7 of
`docs/HTML-PACKAGE-PLAN.md`, rulings HP-12 and HP-13). The inputs are the
projection of `Gates.HtmlStandard` and the authored readings of
`Whatwg.Html.Schema.Readings`; the gate refuses a reading whose block digest
no longer matches the projection. The outputs, all drift-checked by
`lake exe htmlstandard`:

- `Whatwg/Html/Schema/Tags.lean`: the tag universe (the standard's 113
  elements in source order, and text), markup names both ways, the void set
  from the standard's own list, and the transparent set;
- `Whatwg/Html/Schema/Families.lean`: the standard's categories, the bases
  (the distinct base memberships the readings name), each element's own
  base and descendant exclusions, the base overrides, and the labelled
  direct children;
- `Whatwg/Html/Schema/Attributes.lean`: the attribute universe, kinds,
  per-element sets, helper rows, and the name lookup;
- `Whatwg/Html/Schema/ContentModel.lean`: one row per element;
- `Whatwg/Html/Node/Combinators.lean`: one combinator per element and one
  helper per attribute, uniform.

## Contexts

A position in a document is a context: a base, the exclusions inherited
from every ancestor, and the direct children a parent admits besides. An
element's own reading gives its base and its exclusions; a transparent
element has no base of its own and takes its context's. The context a
child is checked in is computed by `Whatwg.Html.Content.Ctx.child`, so no
closure of sets exists any more; the checker `validIn` and the typed tree
both read these tables.
-/

namespace Gates.HtmlStandardEmit

open Gates.Common Gates.HtmlStandard
open Whatwg.Html.Schema.Readings (BaseKind Model Reading Transparent)

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

/-! ## Readings applied -/

def catNameOf : String → String
  | "interactive" => catInteractive | "heading" => catHeading | "sectioning" => catSectioning | c => c

/-- Membership of a tag in a base, over the projection's categories. -/
def baseAdmits (rows : List Row) (b : BaseKind) (plusTags plusCats : List String) (tag : String) : Bool :=
  let cat (c : String) : Bool := if c == "media" then mediaElements.contains tag else catOf rows (catNameOf c) tag
  let isText := tag == textTag
  let base := match b with
    | .flow => isText || cat "Flow content."
    | .phrasing => isText || cat "Phrasing content."
    | .text => isText
    | .nothing => false
    | .metadata => cat "Metadata content."
    | .only names ss => names.contains tag || (ss && (tag == "script" || tag == "template"))
  base || plusTags.contains tag || plusCats.any cat

def sortStrings (xs : List String) : List String :=
  (xs.eraseDups.toArray.qsort (· < ·)).toList

/-- A base: a `BaseKind` with what the reading adds to it. Two bases with the
same members are one base, named by the first reading that reached it. -/
structure Base where
  name : String
  kind : BaseKind
  plusTags : List String
  plusCats : List String
  members : List String
  deriving Repr, Inhabited

def kindName : BaseKind → String
  | .flow => "flow" | .phrasing => "phrasing" | .text => "text" | .nothing => "nothing"
  | .metadata => "metadata"
  | .only names ss => "only_" ++ "_".intercalate names ++ (if ss then "" else "_strict")

def baseName (k : BaseKind) (plusTags plusCats : List String) : String :=
  kindName k ++ (if plusCats.isEmpty && plusTags.isEmpty then "" else
    "_with_" ++ "_".intercalate (sortStrings plusCats ++ sortStrings plusTags))

/-- The reading of a row: the mechanical reading, else the authored one,
whose digest must be the block's. -/
def modelOf (r : Row) : Except String (Model × String) := do
  match Whatwg.Html.Schema.Readings.readings.find? (·.name == r.name) with
  | some rd =>
    unless rd.digest == r.digest do
      throw s!"html standard emit: the reading of `{r.name}` is pinned to digest {rd.digest} but the block now has {r.digest}; re-examine the reading"
    return (rd.model, "authored: " ++ rd.note)
  | none =>
    match Whatwg.Html.Schema.Readings.sentenceModel r.contentModel with
    | some m => return (m, "sentence")
    | none => throw s!"html standard emit: no reading for `{r.name}`: {r.contentModel}"

def isTransparent (name : String) : Bool :=
  Whatwg.Html.Schema.Readings.transparents.any (·.name == name)

structure ElementOut where
  row : Row
  model : Model
  transparent : Bool
  reading : String
  baseName : String
  deriving Repr, Inhabited

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
  Whatwg.Html.Schema.Readings.extraAttrs.map fun (m, k, d) => (m, if k == "prefix" then .prefix else .text, d)

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

structure Schema where
  rows : List Row
  attrs : List AttrOut
  tags : List String
  voidTags : List String
  voidDigest : String
  elements : List ElementOut
  bases : List Base
  deriving Repr, Inhabited

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
  let tags := rows.map (·.name) ++ [textTag]
  let lift {α} : Except String α → IO α
    | .ok v => pure v
    | .error e => throw <| IO.userError e
  let (voidTags, voidDigest) ← lift (voidList text)
  -- bases: the seeds, then every element's own base, deduplicated by members
  let mut bases : Array Base := #[]
  let addBase (bs : Array Base) (k : BaseKind) (plusTags plusCats : List String) : Array Base × String :=
    let members := tags.filter (baseAdmits rows k plusTags plusCats)
    match bs.find? (·.members == members) with
    | some b => (bs, b.name)
    | none =>
      let nm := baseName k plusTags plusCats
      (bs.push { name := nm, kind := k, plusTags, plusCats, members }, nm)
  for k in [BaseKind.flow, .phrasing, .metadata, .text, .nothing, .only ["html"] false] do
    let (bs, _) := addBase bases k [] []
    bases := bs
  -- the document root base is the last seed; rename it
  bases := bases.map fun b => if b.kind == .only ["html"] false then { b with name := "document" } else b
  let mut elements : Array ElementOut := #[]
  for r in rows do
    let (m, reading) ← lift (modelOf r)
    let (bs, nm) := addBase bases m.base m.plusTags m.plusCats
    bases := bs
    elements := elements.push { row := r, model := m, transparent := isTransparent r.name, reading, baseName := nm }
  for (_, _, k) in Whatwg.Html.Schema.Readings.baseOverrides do
    let (bs, _) := addBase bases k [] []
    bases := bs
  return { rows, attrs, tags, voidTags, voidDigest, elements := elements.toList, bases := bases.toList }

/-! ## Emission -/

def header (moduleName : String) (summary : String) (imports : List String := []) : String :=
  String.join (imports.map fun m => s!"import {m}\n") ++ (if imports.isEmpty then "" else "\n") ++
  s!"/-!\n# {moduleName}\n\n{summary}\n\n" ++
  "GENERATED by `lake exe htmlstandard --write` from the sealed HTML Standard\n" ++
  s!"`{source.relative}` (SHA-256 `{source.digest}`), through the projection\n" ++
  "`generated/html-standard-elements.tsv` and the readings of\n" ++
  "`Whatwg/Html/Schema/Readings.lean`. DO NOT EDIT: `lake exe htmlstandard` fails on\n" ++
  "any byte of drift. Slice H7 of `docs/HTML-PACKAGE-PLAN.md`, rulings HP-12 and HP-13.\n" ++
  "Data and derived instances only: no proof lives here.\n-/\n\n"

def baseOfName (s : Schema) (k : BaseKind) (plusTags plusCats : List String) : String :=
  let members := s.tags.filter (baseAdmits s.rows k plusTags plusCats)
  match s.bases.find? (·.members == members) with
  | some b => b.name
  | none => baseName k plusTags plusCats

def emitTags (s : Schema) : String :=
  header "Whatwg.Html.Schema.Tags"
    "The element-tag universe: every element the HTML Standard defines at the\npin, in the order of `source`, and `pcdata`, the text pseudo-tag." ++
  "namespace Whatwg.Html.Schema\n\n" ++
  emitEnum "Tag" "An element tag of the standard, or text." s.tags ++
  emitAll "Tag.all" "Every tag, in source order." "Tag" s.tags ++
  emitStringFn "Tag.variantName" "The tag's name: its markup name, or `pcdata` for text." "Tag" (s.tags.map fun t => (t, t)) ++
  "/-- The markup name of an element tag; `none` for text. -/\ndef Tag.markupName : Tag → Option String\n" ++
  "\n".intercalate (s.rows.map fun r => s!"  | .{ctorName r.name} => some \"{r.name}\"") ++ "\n  | _ => none\n\n" ++
  "/-- The tag of a markup name; `none` for any other string. -/\ndef Tag.ofName? : String → Option Tag\n" ++
  "\n".intercalate (s.rows.map fun r => s!"  | \"{r.name}\" => some .{ctorName r.name}") ++ "\n  | _ => none\n\n" ++
  emitBoolSet "Tag.isVoid"
    (s!"The void elements, from the standard's own list (`Void elements` in the\nsyntax section, span digest `{s.voidDigest}`).") "Tag" s.voidTags s.tags ++
  emitBoolSet "Tag.isTransparent" "The transparent elements: their content is their context's, minus what they exclude (`Whatwg.Html.Schema.Readings.transparents`)." "Tag"
    (Whatwg.Html.Schema.Readings.transparents.map (·.name)) s.tags ++
  "end Whatwg.Html.Schema\n"

def exclLiteral (minusTags minusCats : List String) : String :=
  let flags := (minusCats.map fun c => c) ++ minusTags
  if flags.isEmpty then "{}" else
    "{ " ++ ", ".intercalate (flags.map fun f => s!"{f} := true") ++ " }"

def emitFamilies (s : Schema) : String := Id.run do
  let mut out := header "Whatwg.Html.Schema.Families"
    "The standard's categories as membership functions, the bases (every\ndistinct base membership the readings name) as membership functions, each\nelement's own base and descendant exclusions, the base overrides, and the\nlabelled direct children."
    ["Whatwg.Html.Schema.Tags", "Whatwg.Html.Schema.Exclusions"]
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
  let names := s.bases.map (·.name)
  out := out ++ emitEnum "Base" "A base of a context: a distinct membership the readings name. `document` admits `html` alone." names
  out := out ++ emitAll "Base.all" "Every base." "Base" names
  out := out ++ emitStringFn "Base.name" "The base's name." "Base" (names.map fun n => (n, n))
  for b in s.bases do
    out := out ++ emitBoolSet s!"Bases.{b.name}" s!"`{b.name}`: {b.members.length} of {s.tags.length} tags." "Tag" b.members s.tags
  out := out ++ "/-- Membership, dispatching to the base's own function. -/\ndef Base.contains : Base → Tag → Bool\n" ++
    "\n".intercalate (names.map fun n => s!"  | .{ctorName n}, t => Bases.{n} t") ++ "\n\n"
  out := out ++ "/-- The own base of an element: what its children are checked against when\nit is not transparent (a transparent element's own base is its reading in\nflow context, used at a root). `nothing` for text. -/\ndef Tag.ownBase : Tag → Base\n" ++
    "\n".intercalate (s.elements.map fun e => s!"  | .{ctorName e.row.name} => .{ctorName e.baseName}") ++ "\n  | .pcdata => .nothing\n\n"
  out := out ++ "/-- The descendant exclusions an element adds to its context. -/\ndef Tag.ownExcl : Tag → Exclusions\n" ++
    "\n".intercalate (s.elements.filterMap fun e =>
      let t := Whatwg.Html.Schema.Readings.transparents.find? (·.name == e.row.name)
      let minusTags := e.model.minusTags ++ (t.map (·.minusTags)).getD []
      let minusCats := e.model.minusCats ++ (t.map (·.minusCats)).getD []
      if minusTags.isEmpty && minusCats.isEmpty then none
      else some s!"  | .{ctorName e.row.name} => {exclLiteral (sortStrings minusTags) (sortStrings minusCats)}") ++
    "\n  | _ => {}\n\n"
  out := out ++ "/-- A transparent element whose base in one context is not the context's. -/\ndef Base.override : Base → Tag → Option Base\n" ++
    "\n".intercalate (Whatwg.Html.Schema.Readings.baseOverrides.map fun (b, t, k) =>
      s!"  | .{ctorName b}, .{ctorName t} => some .{ctorName (baseOfName s k [] [])}") ++ "\n  | _, _ => none\n\n"
  out := out ++ "/-- The direct children a sentence admits first and outside any base\n(`source` and `track` under `audio` and `video`, `area` under `map`). -/\ndef labelledChild : Tag → Tag → Bool\n" ++
    "\n".intercalate (Whatwg.Html.Schema.Readings.labelled.map fun (p, c) => s!"  | .{ctorName p}, .{ctorName c} => true") ++ "\n  | _, _ => false\n\n"
  let parents := (Whatwg.Html.Schema.Readings.labelled.map (·.1)).eraseDups
  out := out ++ "/-- The labelled direct children of a parent, as a list. -/\ndef Tag.labelled : Tag → List Tag\n" ++
    "\n".intercalate (parents.map fun p =>
      let cs := (Whatwg.Html.Schema.Readings.labelled.filter (·.1 == p)).map (·.2)
      s!"  | .{ctorName p} => [" ++ ", ".intercalate (cs.map fun c => "." ++ ctorName c) ++ "]") ++ "\n  | _ => []\n\n"
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
  out := out ++ "/-- The attribute of a markup name; `none` for any other string (the\nprefixes are matched by `String.startsWith` in the checker, not here). -/\ndef Attr.ofName? : String → Option Attr\n" ++
    "\n".intercalate ((names.filter fun n => !n.endsWith "-").map fun n => s!"  | \"{n}\" => some .{ctorName n}") ++ "\n  | _ => none\n\n"
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

def emitContentModel (s : Schema) : String :=
  let rows := s.elements.map fun e =>
    "   { name := \"" ++ e.row.name ++ "\", tag := ." ++ ctorName e.row.name ++ ", kind := ." ++
      (if s.voidTags.contains e.row.name || e.model.base == .nothing then "nullary" else "star") ++
      ", transparent := " ++ toString e.transparent ++ ", base := ." ++ ctorName e.baseName ++
      ", attribs := ." ++ ctorName (e.row.name ++ "_attrib") ++ ",\n     digest := \"" ++ e.row.digest ++ "\", reading := " ++ e.reading.quote ++ " }"
  header "Whatwg.Html.Schema.ContentModel"
    "One row per element of the standard: its tag, whether it takes children,\nwhether it is transparent, its own base (`Tag.ownBase`; its exclusions are\n`Tag.ownExcl`), its attribute set, the span digest of its definition, and\nthe reading its sentence was given: `sentence` when read mechanically,\n`authored: ...` otherwise."
    ["Whatwg.Html.Schema.Tags", "Whatwg.Html.Schema.Families", "Whatwg.Html.Schema.Attributes"] ++
  "namespace Whatwg.Html.Schema\n\n" ++
  "/-- Whether an element takes children. -/\ninductive ElementKind where\n  | star | nullary\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
  "/-- One element of the standard. -/\nstructure Element where\n  name : String\n  tag : Tag\n  kind : ElementKind\n  transparent : Bool\n  base : Base\n  attribs : AttrSet\n  digest : String\n  reading : String\n  deriving Repr, Inhabited\n\n" ++
  "/-- Every element, in source order. -/\ndef elements : List Element :=\n  [" ++ dropChars (",\n".intercalate rows) 3 ++ "]\n\n" ++
  "/-- The position in `elements` of a tag; `none` for text. -/\ndef Tag.elementIndex? : Tag → Option Nat\n" ++
  "\n".intercalate (s.elements.zipIdx.map fun (e, i) => s!"  | .{ctorName e.row.name} => some {i}") ++ "\n  | _ => none\n\n" ++
  "/-- The element of a tag. -/\ndef Tag.element? (t : Tag) : Option Element :=\n  t.elementIndex?.bind (elements[·]?)\n\n" ++
  "/-- The attribute set of a tag, as one flat match; `none` for text. -/\ndef Tag.attribs? : Tag → Option AttrSet\n" ++
  "\n".intercalate (s.elements.map fun e => s!"  | .{ctorName e.row.name} => some .{ctorName (e.row.name ++ "_attrib")}") ++ "\n  | _ => none\n\n" ++
  "end Whatwg.Html.Schema\n"

def emitCombinators (s : Schema) : String := Id.run do
  let mut out := "import Whatwg.Html.Node.Typed\nimport Whatwg.Html.Node.Admit\n\n/-!\n# Whatwg.Html.Node.Combinators\n\nOne combinator per element of the standard, in source order, the two text\nconstructors, `el`, and one helper per attribute of the standard. Every\ncombinator has the same shape: it is polymorphic in the context `ctx` it is\nplaced in, its children are `Child (ctx.child <tag>)`, then `attrs` with a\ndefault of `[]`, then the attribute obligation `_ha` discharged by the\n`admits` tactic; a void or childless element has no children parameter. A\nroot names its context: `E.html : Element .html Ctx.document`. The names\nlive in `Whatwg.Html.E` and `Whatwg.Html.A` because a dozen are single\nletters.\n\n" ++
    "GENERATED by `lake exe htmlstandard --write` (see `Gates/HtmlStandardEmit.lean`).\nDO NOT EDIT: `lake exe htmlstandard` fails on any byte of drift.\n-/\n\nnamespace Whatwg.Html.E\n\nopen Whatwg.Html.Schema (Tag Attr AttrSet)\nopen Whatwg.Html.Content (Ctx)\n\n" ++
    "/-- A text run, admitted where the context's base names text. -/\ndef txt {ctx : Ctx} (s : String)\n    (h : ctx.admits .pcdata = true := by admits) : Child ctx :=\n  Child.text s h\n\n" ++
    "/-- A named entity reference, admitted where text is. -/\ndef entity {ctx : Ctx} (name : String)\n    (h : ctx.admits .pcdata = true := by admits) : Child ctx :=\n  Child.entity name h\n\n" ++
    "/-- Place a typed element in a child position: `Child.of` under a short name. -/\ndef el {ctx : Ctx} {t : Tag} (e : Element t ctx)\n    (h : ctx.admits t = true := by admits) : Child ctx :=\n  Child.of e h\n\n"
  for e in s.elements do
    let n := ctorName e.row.name
    let tag := "." ++ n
    let nullary := s.voidTags.contains e.row.name || e.model.base == .nothing
    let attrs := s!"    (attrs : List (Attr × String) := [])\n    (_ha : Content.attrsOk {tag} (rawAttrs attrs) = true := by admits) :\n"
    let doc := s!"/-- `{e.row.name}`: {e.reading}. -/\n"
    if nullary then
      out := out ++ doc ++ s!"def {n} " ++ "{ctx : Ctx}\n" ++ attrs ++ s!"    Element {tag} ctx :=\n  Element.ofChildren [] attrs _ha\n\n"
    else
      out := out ++ doc ++ s!"def {n} " ++ "{ctx : Ctx} (children : List (Child (ctx.child " ++ tag ++ ")) := [])\n" ++ attrs ++
        s!"    Element {tag} ctx :=\n  Element.ofChildren children attrs _ha\n\n"
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
  s!"{s.bases.length} bases, {s.voidTags.length} void tags, " ++
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
