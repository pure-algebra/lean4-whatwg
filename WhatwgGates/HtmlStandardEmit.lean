import WhatwgGates.HtmlStandard
import WhatwgGates.EmitLean
import Whatwg.Html.Schema.Readings

/-!
# Gates.HtmlStandardEmit

The content model of `Whatwg.Html`, generated from the HTML Standard's own
element definitions and attribute indexes (slices H6.1 and H7 of
`docs/HTML-PACKAGE-PLAN.md`, rulings HP-12 and HP-13). The inputs are the
projection of `Gates.HtmlStandard` and the authored readings of
`Whatwg.Html.Schema.Readings`; the gate refuses a reading whose block digest
no longer matches the projection. The outputs, all drift-checked by
`lake exe whatwg_htmlstandard`:

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

open Gates.Common Gates.HtmlStandard Gates.EmitLean
open Whatwg.Html.Schema.Readings (BaseKind Model Reading Transparent)

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

/-! ## Attribute conditions on categories -/

/-- The condition a category sentence states, read mechanically from the
three shapes the standard uses; anything else is `always`. -/
def conditionOf (sentence : String) : String :=
  let pre := "If the element has "
  if sentence.startsWith "If the type attribute is not in the Hidden state:" then
    ".attrNot \"type\" \"hidden\""
  else if sentence.startsWith pre then
    match (dropChars sentence pre.length).splitOn " attribute:" with
    | [x, _] =>
      let x := if x.startsWith "an " then dropChars x 3 else if x.startsWith "a " then dropChars x 2 else x
      let names := (x.splitOn " or ").map collapse
      ".hasAny [" ++ ", ".intercalate (names.map String.quote) ++ "]"
    | _ => ".always"
  else if sentence.startsWith "If the " && (sentence.splitOn " attribute is present:").length > 1 then
    match (dropChars sentence 7).splitOn " attribute is present:" with
    | [x, _] => ".hasAny [" ++ (collapse x).quote ++ "]"
    | _ => ".always"
  else ".always"

/-- The conditional sentence a row states for a category, if any. -/
def conditionFor (r : Row) (cat : String) : Option String :=
  r.categories.find? fun c => c != cat && ((c.splitOn (": " ++ cat)).length > 1 || (c.splitOn (": " ++ cat.decapitalize)).length > 1)

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
  | boolean | keywords (isOpen : Bool) | integer | nonNegInteger | float | url | text | namePrefix
  deriving BEq, Repr, Inhabited

def Kind.render : Kind → String
  | .boolean => ".boolean" | .keywords o => s!".keywords {o}" | .integer => ".integer"
  | .nonNegInteger => ".nonNegInteger" | .float => ".float" | .url => ".url" | .text => ".text"
  | .namePrefix => ".namePrefix"

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
  Whatwg.Html.Schema.Readings.extraAttrs.map fun (m, k, d) => (m, if k == "prefix" then .namePrefix else .text, d)

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

/-! ## Foreign content -/

/-- A foreign element that a category list names: `SVG svg` or `MathML math`. -/
structure ForeignTag where
  name : String
  vocabulary : String
  categories : List String
  deriving Repr, Inhabited

/-- What the standard says of foreign content: the foreign elements of its category lists, and
the tables of its tree construction. `digest` is over every span read, in reading order. -/
structure ForeignData where
  tags : List ForeignTag
  breakout : List String
  svgTagNames : List (String × String)
  svgAttrNames : List (String × String)
  foreignAttrs : List (String × String)
  svgIntegrationPoints : List String
  digest : String
  deriving Repr, Inhabited

/-- The text after the one occurrence of `start`, up to the next `stop`. -/
def spanAfter (text start stop what : String) : Except String String :=
  match text.splitOn start with
  | [_, after] => pure (upTo after stop)
  | _ => throw s!"html standard emit: {what} was not found exactly once"

/-- A text without its HTML comments. -/
def stripComments (s : String) : String :=
  match s.splitOn "<!--" with
  | [] => ""
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      match piece.splitOn "-->" with
      | [] => ""
      | _ :: after => "-->".intercalate after)

/-- The contents of each `<code …>…</code>` of a text, in order. -/
def codeCells (s : String) : List String :=
  ((s.splitOn "<code").drop 1).map fun piece =>
    upTo (match piece.splitOn ">" with | [] => "" | _ :: after => ">".intercalate after) "</code>"

/-- The rows of a table's body, each as its `<code>` cells. -/
def tableCells (table : String) : List (List String) :=
  let body := match table.splitOn "<tbody>" with | [] => "" | _ :: after => "<tbody>".intercalate after
  ((body.splitOn "<tr>").drop 1).map codeCells

/-- The category lists of "Kinds of content": each heading, with the category it lists. -/
def categoryHeadings : List (String × String) :=
  [("<h6>Metadata content</h6>", catMetadata), ("<h6>Flow content</h6>", catFlow),
   ("<h6>Sectioning content</h6>", catSectioning), ("<h6>Heading content</h6>", catHeading),
   ("<h6>Phrasing content</h6>", catPhrasing), ("<h6>Embedded content</h6>", catEmbedded),
   ("<h6>Interactive content</h6>", catInteractive),
   ("<h6 id=\"palpable-content\">Palpable content</h6>", catPalpable),
   ("<h6>Script-supporting elements</h6>", catScriptSupporting)]

/-- A foreign item of a category list, `<span>SVG <code>svg</code></span>`: the vocabulary and
the element name. An item of any other shape is no foreign item. -/
def foreignItem (item : String) : Option (String × String) :=
  if !item.startsWith "<span>" then none else
  match (upTo (dropChars item 6) "</span>").splitOn " <code>" with
  | [vocabulary, rest] => some (vocabulary, upTo rest "</code>")
  | _ => none

/-- Everything the standard says of foreign content that the schema holds (rulings SV-7 and
SV-17 of `docs/SVG-PACKAGE-PLAN.md`). Each span is found by an anchor that occurs once. -/
def foreignOf (text : String) : Except String ForeignData := do
  let mut spans : List String := []
  -- the category lists
  let mut found : List (String × String × String) := []
  for (heading, category) in categoryHeadings do
    let list ← spanAfter text heading "</ul>" s!"the category list under {heading}"
    spans := spans ++ [list]
    for item in (list.splitOn "<li>").drop 1 do
      match foreignItem item with
      | some (vocabulary, name) =>
        unless vocabulary == "SVG" || vocabulary == "MathML" do
          throw s!"html standard emit: the category list under {heading} names the unknown vocabulary `{vocabulary}`"
        found := found ++ [(name, vocabulary, category)]
      | none => pure ()
  let names := (found.map (·.1)).eraseDups
  let tags := names.map fun name =>
    { name
      vocabulary := ((found.find? (·.1 == name)).map (·.2.1)).getD ""
      categories := (found.filter (·.1 == name)).map (·.2.2) : ForeignTag }
  -- the start tags that end foreign content
  let breakoutSpan ← spanAfter text "<dt>A start tag whose tag name is one of: <!--\"a\",-->" "</dt>"
    "the list of start tags that end foreign content"
  let quoted := (stripComments breakoutSpan).splitOn "\""
  let breakout := (quoted.zipIdx.filter fun (_, i) => i % 2 == 1).map (·.1)
  -- the three tables of the tree construction
  let pairs (table what : String) : Except String (List (String × String)) :=
    (tableCells table).mapM fun cells =>
      match cells with
      | [lower, restored] => pure (lower, restored)
      | _ => throw s!"html standard emit: a row of {what} does not hold two names"
  let tagSpan ← spanAfter text "SVG elements that are not all lowercase.)" "</table>"
    "the table of SVG tag names"
  let attrSpan ← spanAfter text "<dfn>adjust SVG attributes</dfn>" "</table>"
    "the table of SVG attribute names"
  let foreignSpan ← spanAfter text "<dfn>adjust foreign attributes</dfn>" "</table>"
    "the table of foreign attributes"
  let svgTagNames ← pairs tagSpan "the table of SVG tag names"
  let svgAttrNames ← pairs attrSpan "the table of SVG attribute names"
  let foreignAttrs ← (((foreignSpan.splitOn "<tbody>").drop 1 |> "<tbody>".intercalate).splitOn "<tr>" |>.drop 1).mapM
    fun row =>
      match codeCells row, row.splitOn "<span>" with
      | name :: _, [_, namespaced] => pure (name, upTo namespaced "</span>")
      | _, _ => throw "html standard emit: a row of the table of foreign attributes was not read"
  -- the integration points
  let pointSpan ← spanAfter text "<dfn>HTML integration point</dfn>" "</ul>"
    "the list of HTML integration points"
  let svgIntegrationPoints := ((pointSpan.splitOn "<li>").drop 1).filterMap fun item =>
    match item.splitOn "<span>SVG <code>" with
    | [_, rest] => some (upTo rest "</code>")
    | _ => none
  spans := spans ++ [breakoutSpan, tagSpan, attrSpan, foreignSpan, pointSpan]
  if tags.isEmpty || breakout.isEmpty || svgTagNames.isEmpty || svgAttrNames.isEmpty ||
      foreignAttrs.isEmpty || svgIntegrationPoints.isEmpty then
    throw "html standard emit: a table of foreign content was read as empty"
  return { tags, breakout, svgTagNames, svgAttrNames, foreignAttrs, svgIntegrationPoints
           digest := Gates.Sha256.hexDigestOfString (String.join spans) }

/-- A foreign tag as a row that states its categories and nothing else, so that category
membership is one function over elements and foreign tags. -/
def ForeignTag.row (f : ForeignTag) : Row :=
  { name := f.name, line := 0, digest := "", categories := f.categories, contexts := []
    contentModel := [], attributes := [] }

/-! ## The schema -/

structure Schema where
  rows : List Row
  catRows : List Row
  foreign : ForeignData
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
  let lift {α} : Except String α → IO α
    | .ok v => pure v
    | .error e => throw <| IO.userError e
  let foreign ← lift (foreignOf text)
  for f in foreign.tags do
    if rows.any (·.name == f.name) || f.name == textTag then
      throw <| IO.userError s!"html standard emit: the foreign element `{f.name}` has the name of an HTML tag"
  let tags := rows.map (·.name) ++ foreign.tags.map (·.name) ++ [textTag]
  let catRows := rows ++ foreign.tags.map (·.row)
  let (voidTags, voidDigest) ← lift (voidList text)
  -- bases: the seeds, then every element's own base, deduplicated by members
  let mut bases : Array Base := #[]
  let addBase (bs : Array Base) (k : BaseKind) (plusTags plusCats : List String) : Array Base × String :=
    let members := tags.filter (baseAdmits catRows k plusTags plusCats)
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
  for q in Whatwg.Html.Schema.Readings.sequences do
    match rows.find? (·.name == q.name) with
    | some r =>
      unless q.digest == r.digest do
        throw <| IO.userError s!"html standard emit: the sequence reading of `{q.name}` is pinned to digest {q.digest} but the block now has {r.digest}; re-examine the reading"
    | none => throw <| IO.userError s!"html standard emit: the sequence reading of `{q.name}` names no element"
  for (_, _, k) in Whatwg.Html.Schema.Readings.baseOverrides do
    let (bs, _) := addBase bases k [] []
    bases := bs
  return { rows, catRows, foreign, attrs, tags, voidTags, voidDigest, elements := elements.toList,
           bases := bases.toList }

/-! ## Emission -/

def header (moduleName : String) (summary : String) (imports : List String := []) : String :=
  String.join (imports.map fun m => s!"import {m}\n") ++ (if imports.isEmpty then "" else "\n") ++
  s!"/-!\n# {moduleName}\n\n{summary}\n\n" ++
  "GENERATED by `lake exe whatwg_htmlstandard --write` from the sealed HTML Standard\n" ++
  s!"`{source.relative}` (SHA-256 `{source.digest}`), through the projection\n" ++
  "`generated/html-standard-elements.tsv` and the readings of\n" ++
  "`Whatwg/Html/Schema/Readings.lean`. DO NOT EDIT: `lake exe whatwg_htmlstandard` fails on\n" ++
  "any byte of drift. Slice H7 of `docs/HTML-PACKAGE-PLAN.md`, rulings HP-12 and HP-13.\n" ++
  "Data and derived instances only: no proof lives here.\n-/\n\n"

def baseOfName (s : Schema) (k : BaseKind) (plusTags plusCats : List String) : String :=
  let members := s.tags.filter (baseAdmits s.catRows k plusTags plusCats)
  match s.bases.find? (·.members == members) with
  | some b => b.name
  | none => baseName k plusTags plusCats

def emitTags (s : Schema) : String :=
  header "Whatwg.Html.Schema.Tags"
    "The element-tag universe: every element the HTML Standard defines at the\npin, in the order of `source`; the foreign elements that its category lists\nname, `MathML math` and `SVG svg`; and `pcdata`, the text pseudo-tag. A\nforeign tag and `pcdata` have no markup name: no HTML element has one's name." ++
  "namespace Whatwg.Html.Schema\n\n" ++
  emitEnum "Tag" "An element tag of the standard, a foreign element of its category lists, or text." s.tags ++
  emitAll "Tag.all" "Every tag, in source order." "Tag" s.tags ++
  emitStringFn "Tag.variantName" "The tag's name: its markup name, or `pcdata` for text." "Tag" (s.tags.map fun t => (t, t)) ++
  "/-- The markup name of an element tag; `none` for text. -/\ndef Tag.markupName : Tag → Option String\n" ++
  "\n".intercalate (s.rows.map fun r => s!"  | .{ctorName r.name} => some \"{r.name}\"") ++ "\n  | _ => none\n\n" ++
  "/-- The tag of a markup name spelled as characters; `none` for any other\nlist. A `List Char` match compiles to a character-by-character decision\ntree, which the kernel walks in about the same time for every name, where a\n`String` match compares against every earlier arm (performance review §4). -/\ndef Tag.ofChars? : List Char → Option Tag\n" ++
  "\n".intercalate (s.rows.map fun r => s!"  | {charsPattern r.name} => some .{ctorName r.name}") ++ "\n  | _ => none\n\n" ++
  "/-- The tag of a markup name; `none` for any other string. -/\ndef Tag.ofName? (s : String) : Option Tag := Tag.ofChars? s.toList\n\n" ++
  "/-- The name of a foreign element of the category lists (\"Kinds of content\"); `none` for an\nHTML element and for text. -/\ndef Tag.foreignName : Tag → Option String\n" ++
  "\n".intercalate (s.foreign.tags.map fun f => s!"  | .{ctorName f.name} => some \"{f.name}\"") ++ "\n  | _ => none\n\n" ++
  "/-- The foreign tag of a name spelled as characters; `none` for any other list. -/\ndef Tag.ofForeignChars? : List Char → Option Tag\n" ++
  "\n".intercalate (s.foreign.tags.map fun f => s!"  | {charsPattern f.name} => some .{ctorName f.name}") ++ "\n  | _ => none\n\n" ++
  "/-- The foreign tag of a name; `none` for any other string. -/\ndef Tag.ofForeignName? (s : String) : Option Tag := Tag.ofForeignChars? s.toList\n\n" ++
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
    ["Whatwg.Html.Schema.Tags", "Whatwg.Html.Schema.Exclusions", "Whatwg.Html.Schema.Condition"]
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  for (fn, cat, doc) in [("Cats.flow", catFlow, "Flow content"), ("Cats.phrasing", catPhrasing, "Phrasing content"),
      ("Cats.heading", catHeading, "Heading content"), ("Cats.sectioning", catSectioning, "Sectioning content"),
      ("Cats.interactive", catInteractive, "Interactive content, with the conditional cases read as interactive"),
      ("Cats.metadata", catMetadata, "Metadata content"), ("Cats.embedded", catEmbedded, "Embedded content"),
      ("Cats.palpable", catPalpable, "Palpable content, with the conditional cases read as palpable"),
      ("Cats.scriptSupporting", catScriptSupporting, "Script-supporting elements")] do
    out := out ++ emitBoolSet fn (doc ++ ", by the `Categories` entries of the projection, and by the\nforeign items of the standard's category list.") "Tag"
      (s.catRows.filter (hasCat · cat) |>.map (·.name)) s.tags
  out := out ++ emitBoolSet "Cats.media" "The media elements, `audio` and `video`." "Tag" mediaElements s.tags
  for (fn, cat, doc) in [("Tag.interactiveIf", catInteractive, "interactive content"), ("Tag.flowIf", catFlow, "flow content"), ("Tag.phrasingIf", catPhrasing, "phrasing content")] do
    let rows := s.rows.filterMap fun r => (conditionFor r cat).map fun c => (r.name, c)
    out := out ++ s!"/-- The attribute condition under which a tag is {doc}, for the tags whose\ncategory is conditional in the projection; `none` where it is unconditional.\nA sentence not read mechanically is `always`. -/\ndef {fn} : Tag → Option Condition\n" ++
      "\n".intercalate (rows.map fun (n, c) => s!"  | .{ctorName n} => some ({conditionOf c})") ++ "\n  | _ => none\n\n"
  let names := s.bases.map (·.name)
  out := out ++ emitEnum "Base" "A base of a context: a distinct membership the readings name. `document` admits `html` alone." names
  out := out ++ emitAll "Base.all" "Every base." "Base" names
  out := out ++ emitStringFn "Base.name" "The base's name." "Base" (names.map fun n => (n, n))
  for b in s.bases do
    out := out ++ emitBoolSet s!"Bases.{b.name}" s!"`{b.name}`: {b.members.length} of {s.tags.length} tags." "Tag" b.members s.tags
  out := out ++ "/-- Membership, dispatching to the base's own function. -/\ndef Base.contains : Base → Tag → Bool\n" ++
    "\n".intercalate (names.map fun n => s!"  | .{ctorName n}, t => Bases.{n} t") ++ "\n\n"
  out := out ++ "/-- The own base of an element: what its children are checked against when\nit is not transparent (a transparent element's own base is its reading in\nflow context, used at a root). `nothing` for text and for a foreign tag,\nwhose children the seam checks. -/\ndef Tag.ownBase : Tag → Base\n" ++
    "\n".intercalate (s.elements.map fun e => s!"  | .{ctorName e.row.name} => .{ctorName e.baseName}") ++ "\n" ++
    String.join (s.foreign.tags.map fun f => s!"  | .{ctorName f.name} => .nothing\n") ++ "  | .pcdata => .nothing\n\n"
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
  out := out ++ "/-- The kind of an attribute's value, read from the index's `Value` cell:\na boolean attribute; a keyword list (`open` when the cell also admits\nvalues the list does not spell); an integer; a non-negative integer; a\nfloating-point number; a URL; text; or a prefix. -/\ninductive AttrValueKind where\n  | boolean | keywords (isOpen : Bool) | integer | nonNegInteger | float | url | text | namePrefix\n  deriving DecidableEq, Repr, Inhabited\n\n"
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
  out := out ++ "/-- The attribute of a markup name spelled as characters (the prefixes are\nmatched by prefix in the checker, not here); a character decision tree, see\n`Tag.ofChars?`. -/\ndef Attr.ofChars? : List Char → Option Attr\n" ++
    "\n".intercalate ((names.filter fun n => !n.endsWith "-").map fun n => s!"  | {charsPattern n} => some .{ctorName n}") ++ "\n  | _ => none\n\n" ++
    "/-- The attribute of a markup name; `none` for any other string. -/\ndef Attr.ofName? (s : String) : Option Attr := Attr.ofChars? s.toList\n\n"
  -- the rows of each attribute, as one flat match, so a lookup does not filter all rows
  out := out ++ "/-- The index rows of an attribute, as one flat match over `Attr`: the same\nrows as `attributeRows.filter (·.attr == a)`, so that a value check reads a\nhandful of rows instead of filtering the whole index (performance review §4). -/\ndef Attr.indexRows : Attr → List AttrRow\n" ++
    "\n".intercalate (names.map fun n =>
      let mine := s.attrs.filter (·.markup == n)
      let extra := extraAttrs.filter (fun (m, _, _) => m == n)
      -- one row per line: a structure instance continued on a second line does
      -- not parse inside a match alternative
      let oneLine (r : String) : String := collapse (r.replace "\n" " ")
      let rowsText := (mine.map fun o => oneLine (rowText o)) ++ (extra.map fun (m, k, d) =>
        "{ attr := ." ++ ctorName m ++ ", markup := " ++ m.quote ++ ", handler := false, elements := [], global := true, kind := " ++ k.render ++ ", keywords := [], allowEmpty := false, description := " ++ d.quote ++ ", digest := \"\" }")
      s!"  | .{ctorName n} =>\n    [" ++ ",\n     ".intercalate rowsText ++ "]") ++ "\n\n"
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

/-- A reading's sequence as Lean source over `Tag`. -/
def seqExpr : Whatwg.Html.Schema.Readings.Seq → String
  | .eps => ".eps"
  | .tag n => s!"(.tag .{ctorName n})"
  | .base ex => "(.base [" ++ ", ".intercalate (ex.map fun n => "." ++ ctorName n) ++ "])"
  | .seq a b => s!"(.seq {seqExpr a} {seqExpr b})"
  | .alt a b => s!"(.alt {seqExpr a} {seqExpr b})"
  | .star a => s!"(.star {seqExpr a})"
  | .opt a => s!"(.opt {seqExpr a})"
  | .plus a => s!"(.plus {seqExpr a})"

def emitContentModel (s : Schema) : String :=
  let rows := s.elements.map fun e =>
    "   { name := \"" ++ e.row.name ++ "\", tag := ." ++ ctorName e.row.name ++ ", kind := ." ++
      (if s.voidTags.contains e.row.name || e.model.base == .nothing then "nullary" else "star") ++
      ", transparent := " ++ toString e.transparent ++ ", base := ." ++ ctorName e.baseName ++
      ", attribs := ." ++ ctorName (e.row.name ++ "_attrib") ++ ",\n     digest := \"" ++ e.row.digest ++ "\", reading := " ++ e.reading.quote ++ " }"
  header "Whatwg.Html.Schema.ContentModel"
    "One row per element of the standard: its tag, whether it takes children,\nwhether it is transparent, its own base (`Tag.ownBase`; its exclusions are\n`Tag.ownExcl`), its attribute set, the span digest of its definition, and\nthe reading its sentence was given: `sentence` when read mechanically,\n`authored: ...` otherwise."
    ["Whatwg.Html.Schema.Tags", "Whatwg.Html.Schema.Families", "Whatwg.Html.Schema.Attributes", "Whatwg.Html.Schema.Sequence"] ++
  "namespace Whatwg.Html.Schema\n\n" ++
  "/-- Whether an element takes children. -/\ninductive ElementKind where\n  | star | nullary\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
  "/-- One element of the standard. -/\nstructure Element where\n  name : String\n  tag : Tag\n  kind : ElementKind\n  transparent : Bool\n  base : Base\n  attribs : AttrSet\n  digest : String\n  reading : String\n  deriving Repr, Inhabited\n\n" ++
  "/-- Every element, in source order. -/\ndef elements : List Element :=\n  [" ++ dropChars (",\n".intercalate rows) 3 ++ "]\n\n" ++
  "/-- The position in `elements` of a tag; `none` for text. -/\ndef Tag.elementIndex? : Tag → Option Nat\n" ++
  "\n".intercalate (s.elements.zipIdx.map fun (e, i) => s!"  | .{ctorName e.row.name} => some {i}") ++ "\n  | _ => none\n\n" ++
  "/-- The element of a tag. -/\ndef Tag.element? (t : Tag) : Option Element :=\n  t.elementIndex?.bind (elements[·]?)\n\n" ++
  "/-- The ordered model of a tag, when its reading is a sequence: the\nsequence and whether script-supporting elements may be intermixed\n(`Whatwg.Html.Schema.Readings.sequences`). -/\ndef Tag.seq? : Tag → Option (Seq × Bool)\n" ++
  "\n".intercalate (Whatwg.Html.Schema.Readings.sequences.map fun q =>
    s!"  | .{ctorName q.name} => some ({seqExpr q.seq}, {q.interleave})") ++ "\n  | _ => none\n\n" ++
  "/-- The attribute set of a tag, as one flat match; `none` for text. -/\ndef Tag.attribs? : Tag → Option AttrSet\n" ++
  "\n".intercalate (s.elements.map fun e => s!"  | .{ctorName e.row.name} => some .{ctorName (e.row.name ++ "_attrib")}") ++ "\n  | _ => none\n\n" ++
  "end Whatwg.Html.Schema\n"

def emitCombinators (s : Schema) : String := Id.run do
  let mut out := "import Whatwg.Html.Node.Typed\nimport Whatwg.Html.Node.Admit\n\n/-!\n# Whatwg.Html.Node.Combinators\n\nOne combinator per element of the standard, in source order, the two text\nconstructors, `el`, and one helper per attribute of the standard (typed by\nits keywords where they are identifier-safe, with a `_str` variant for a\ncomputed value), plus `attr`, `data_` and `aria_`. Every\ncombinator has the same shape: it is polymorphic in the context `ctx` it is\nplaced in, its children are `Child (ctx.child <tag>)`, then `attrs` with a\ndefault of `[]`, then one obligation `_ho` (attributes and ordered model)\ndischarged by the `admits` tactic; a void or childless element has no\nchildren parameter. A\nroot names its context: `E.html : Element .html Ctx.document`. The names\nlive in `Whatwg.Html.E` and `Whatwg.Html.A` because a dozen are single\nletters.\n\n" ++
    "GENERATED by `lake exe whatwg_htmlstandard --write` (see `WhatwgGates/HtmlStandardEmit.lean`).\nDO NOT EDIT: `lake exe whatwg_htmlstandard` fails on any byte of drift.\n-/\n\nnamespace Whatwg.Html.E\n\nopen Whatwg.Html.Schema (Tag Attr AttrSet)\nopen Whatwg.Html.Content (Ctx)\nopen Whatwg.Html (AttrVal)\n\n" ++
    "/-- A text run, admitted where the context's base names text. -/\ndef txt {ctx : Ctx} (s : String)\n    (h : ctx.admits .pcdata = true := by admits) : Child ctx :=\n  Child.text s h\n\n" ++
    "/-- A named entity reference, admitted where text is. -/\ndef entity {ctx : Ctx} (name : String)\n    (h : ctx.admits .pcdata = true := by admits) : Child ctx :=\n  Child.entity name h\n\n" ++
    "/-- Place a typed element in a child position: `Child.of` under a short name. -/\ndef el {ctx : Ctx} {t : Tag} (e : Element t ctx)\n    (h : ctx.admitsWith t (rawAttrs e.attrs) = true := by admits) : Child ctx :=\n  Child.of e h\n\n"
  for e in s.elements do
    let n := ctorName e.row.name
    let tag := "." ++ n
    let nullary := s.voidTags.contains e.row.name || e.model.base == .nothing
    let doc := s!"/-- `{e.row.name}`: {e.reading}. -/\n"
    if nullary then
      out := out ++ doc ++ s!"def {n} " ++ "{ctx : Ctx}\n    (attrs : List AttrVal := [])\n" ++
        s!"    (_ho : Content.elementOk ctx {tag} (rawAttrs attrs) [] = true := by admits) :\n" ++
        s!"    Element {tag} ctx :=\n  Element.ofChildren [] attrs _ho\n\n"
    else
      out := out ++ doc ++ s!"def {n} " ++ "{ctx : Ctx} (children : List (Child (ctx.child " ++ tag ++ ")) := [])\n    (attrs : List AttrVal := [])\n" ++
        s!"    (_ho : Content.elementOk ctx {tag} (rawAttrs attrs) (children.map Child.raw) = true := by admits) :\n" ++
        s!"    Element {tag} ctx :=\n  Element.ofChildren children attrs _ho\n\n"
  -- typed keyword enums, for attributes whose keywords are all identifier-safe
  let names := attrNames s.attrs
  let identSafe (k : String) : Bool :=
    !k.isEmpty && k.toList.all (fun c => c.isLower || c.isDigit) && (k.toList.head?.map Char.isLower).getD false
  let keywordsOf (n : String) : List String :=
    ((s.attrs.filter fun o => o.markup == n && (match o.kind with | .keywords false => true | _ => false)).flatMap (·.keywords)).eraseDups
  let typed (n : String) : Bool :=
    let rows := s.attrs.filter (·.markup == n)
    !rows.isEmpty && rows.all (fun o => match o.kind with | .keywords false => true | _ => false) &&
      (keywordsOf n).all identSafe && !(keywordsOf n).isEmpty
  out := out ++ "end Whatwg.Html.E\n\nnamespace Whatwg.Html.K\n\n/-! Typed keyword values: one enumeration per attribute whose `Value` cell\nis a closed keyword list of identifier-safe words. `toString` is the\nkeyword. -/\n\n"
  for n in names do
    if typed n then
      let ks := keywordsOf n
      out := out ++ s!"/-- The keywords of `{n}`. -/\ninductive {ctorName n} where\n  | " ++ " | ".intercalate (ks.map ctorName) ++
        "\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
        s!"def {ctorName n}.toString : {ctorName n} → String\n" ++ "\n".intercalate (ks.map fun k => s!"  | .{ctorName k} => \"{k}\"") ++ "\n\n"
  out := out ++ "end Whatwg.Html.K\n\nnamespace Whatwg.Html.A\n\nopen Whatwg.Html.Schema (Attr)\n\n" ++
    "/-- Any attribute of the index with any value: the escape hatch. -/\ndef attr (a : Attr) (value : String) : AttrVal := AttrVal.of a value\n\n" ++
    "/-- A custom data attribute `data-<suffix>`. -/\ndef data_ (suffix value : String) : AttrVal := AttrVal.data suffix value\n\n" ++
    "/-- An ARIA attribute `aria-<suffix>`. -/\ndef aria_ (suffix value : String) : AttrVal := AttrVal.aria suffix value\n\n"
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
      out := out ++ s!"/-- `{n}`: {desc}. A boolean attribute: present, with the empty string as its value. -/\ndef {helperName n} : AttrVal := AttrVal.of .{ctorName n} \"\"\n\n"
    else if typed n then
      out := out ++ s!"/-- `{n}`: {desc}. Takes one of its keywords. -/\ndef {helperName n} (value : K.{ctorName n}) : AttrVal := AttrVal.of .{ctorName n} value.toString\n\n" ++
        s!"/-- `{n}` with a computed value. -/\ndef {helperName n}_str (value : String) : AttrVal := AttrVal.of .{ctorName n} value\n\n"
    else
      out := out ++ s!"/-- `{n}`: {desc}. -/\ndef {helperName n} (value : String) : AttrVal := AttrVal.of .{ctorName n} value\n\n"
  out := out ++ "end Whatwg.Html.A\n"
  return out

/-- A list of strings as a Lean literal, wrapped at about a hundred columns. -/
def stringList (items : List String) : String := Id.run do
  let mut done : List String := []
  let mut current := ""
  for item in items do
    if current.isEmpty then current := item
    else if current.length + item.length > 92 then
      done := done ++ [current ++ ","]
      current := item
    else current := current ++ ", " ++ item
  if !current.isEmpty then done := done ++ [current]
  return "[" ++ "\n   ".intercalate done ++ "]"

def emitForeign (s : Schema) : String :=
  let f := s.foreign
  let pair (p : String × String) : String := s!"({p.1.quote}, {p.2.quote})"
  header "Whatwg.Html.Schema.Foreign"
    ("What the standard says of foreign content, as data: the foreign elements of its category\nlists, the start tags that end foreign content, the names that its tree construction\nrestores, and the SVG integration points. The seam `Whatwg/Html/Svg.lean` reads these\n(rulings SV-7 and SV-17 of `docs/SVG-PACKAGE-PLAN.md`). The spans read have the SHA-256\n`" ++ f.digest ++ "`.") ++
  "namespace Whatwg.Html.Schema.Foreign\n\n" ++
  "/-- The foreign elements that the category lists name: each name with its vocabulary. -/\ndef vocabulary : List (String × String) :=\n  " ++
    stringList (f.tags.map fun t => pair (t.name, t.vocabulary)) ++ "\n\n" ++
  "/-- The start tags that end foreign content (\"in foreign content\"). A start tag `font`\nwith a `color`, `face` or `size` attribute ends it too. -/\ndef breakout : List String :=\n  " ++
    stringList (f.breakout.map String.quote) ++ "\n\n" ++
  "/-- The SVG element names that the tree construction restores: the lower-case tag name,\nand the element name. -/\ndef svgTagNames : List (String × String) :=\n  " ++
    stringList (f.svgTagNames.map pair) ++ "\n\n" ++
  "/-- The SVG attribute names that \"adjust SVG attributes\" restores: the lower-case name,\nand the attribute name. -/\ndef svgAttrNames : List (String × String) :=\n  " ++
    stringList (f.svgAttrNames.map pair) ++ "\n\n" ++
  "/-- The attributes that \"adjust foreign attributes\" places in a namespace: the name as a\ndocument writes it, and the namespace. -/\ndef foreignAttrs : List (String × String) :=\n  " ++
    stringList (f.foreignAttrs.map pair) ++ "\n\n" ++
  "/-- The SVG elements that are HTML integration points. -/\ndef svgIntegrationPoints : List String :=\n  " ++
    stringList (f.svgIntegrationPoints.map String.quote) ++ "\n\n" ++
  "end Whatwg.Html.Schema.Foreign\n"

def modulePaths : List String :=
  ["Whatwg/Html/Schema/Tags.lean", "Whatwg/Html/Schema/Families.lean", "Whatwg/Html/Schema/Attributes.lean",
   "Whatwg/Html/Schema/ContentModel.lean", "Whatwg/Html/Node/Combinators.lean",
   "Whatwg/Html/Schema/Foreign.lean"]

structure Emitted where
  schema : Schema
  files : List (String × String)

def emitModules (root : System.FilePath) : IO Emitted := do
  let s ← build root
  return { schema := s, files := modulePaths.zip [emitTags s, emitFamilies s, emitAttributes s, emitContentModel s, emitCombinators s,
      emitForeign s] }

def summarize (s : Schema) : String :=
  let authored := (s.elements.filter fun e => e.reading.startsWith "authored").length
  s!"html standard emit: {s.rows.length} elements ({s.rows.length - authored} read from their sentence, {authored} authored readings), " ++
  s!"{s.bases.length} bases, {s.voidTags.length} void tags, " ++
  s!"{(attrNames s.attrs).length} attributes from {s.attrs.length} index rows, {s.rows.length} attribute sets, " ++
  s!"{s.foreign.tags.length} foreign tags, {s.foreign.breakout.length} start tags that end foreign content\n"

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
      failures := failures ++ [s!"missing generated module {path}; run `lake exe whatwg_htmlstandard --write`"]
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
  "usage: lake exe whatwg_htmlstandard          check the two projections, the data module and the six generated modules against a regeneration\n" ++
  "       lake exe whatwg_htmlstandard --write  regenerate all of them from the sealed HTML Standard source"

/-- Command-line entry, invoked by `whatwgbin/HtmlStandard.lean`: the projection
gate of `Gates.HtmlStandard` first, then the schema modules. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] =>
    let rc ← Gates.HtmlStandard.check root
    if rc != 0 then return rc
    let failures ← check root
    if failures.isEmpty then
      IO.println "PASS html standard emit: the six generated schema modules are byte-identical to a fresh emission"
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
