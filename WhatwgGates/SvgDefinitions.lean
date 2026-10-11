import WhatwgGates.Common
import WhatwgGates.Sha256
import WhatwgGates.Xml

/-!
# Gates.SvgDefinitions

The definitions of SVG 2 as a projection (slice S2 of `docs/SVG-PACKAGE-PLAN.md`, rulings SV-2
and SV-3). The sealed `master/publish.xml` of the pin lists the definitions files of SVG 2.
This module reads each of them and writes four projections, each checked for byte drift:

- `generated/svg-elements.tsv`, one row per `element` entry;
- `generated/svg-categories.tsv`, one row per `elementcategory` and `attributecategory` entry;
- `generated/svg-attributes.tsv`, one row per `attribute` entry, wherever it stands;
- `generated/svg-dangling.tsv`, one row per name that an entry cites and no entry declares.

A row holds the definitions' own words: names, lists and anchors, with white space collapsed.
Nothing is interpreted here. `Gates.SvgDefinitionsEmit` resolves the rows into the schema.

The reader refuses what it does not know: a file whose digest is not the pinned one, a
character outside ASCII (`Gates.Xml.read`), a definitions file that `master/publish.xml` does not list, an XML attribute
outside the lists of `allowedKeys`, and an `element` entry with no content model or with two.
A later pin that adds a field therefore fails here and is read on purpose.

Totality: `Gates.Xml.read` runs on fuel, and every pass here is a fold over its result.
-/

namespace Gates.SvgDefinitions

open Gates.Common
open Gates.Xml (Node)

/-! ## The pin -/

/-- The directory of the pin, under the repository root. -/
def pinDirectory : String := "vendor/w3c-svgwg-47e645ef"

/-- One sealed file: its path under the pin directory, and its SHA-256. -/
structure Input where
  relative : String
  digest : String

/-- The file that lists the definitions files of SVG 2. -/
def publish : Input :=
  { relative := "master/publish.xml"
    digest := "ef196a8fc4646430801a15e943c212bc9f82371bb061e076c79c419df03301f1" }

/-- The definitions files of the pin, in the order `master/publish.xml` lists them. -/
def definitionFiles : List Input :=
  [{ relative := "master/definitions.xml"
     digest := "7db42f32f4c2c3c5d6395737dd20cd91e91a41efccf6b9d545cc5abc7400e34b" },
   { relative := "master/definitions-filters.xml"
     digest := "f96968584136839df0770a6f09049f780b066f1a4b0821dd6664dc50992c696c" },
   { relative := "master/definitions-masking.xml"
     digest := "50a0769cbc0855fa91b3323876a3a8005cd59ffcb6521d7c13cdf936a4de3ac8" },
   { relative := "master/definitions-compositing.xml"
     digest := "c055f400e90888d9f107da62e470c750ba2dcd1d205bfa52f2a29d15f9ed844e" },
   { relative := "specs/animations/master/definitions.xml"
     digest := "bcdd0fc20a13924d423243d6d2fecc28c265d23851c3f7d0ef762ebc917c3385" }]

/-- The notice that the W3C Document License asks of a derived work (ruling SV-21), as the
lines a generated module's header carries. -/
def noticeLines : List String :=
  ["Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from",
   "Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C",
   "Document License, https://www.w3.org/copyright/document-license-2023/"]

/-- The notice on one line, as a projection's header carries it. -/
def notice : String := " ".intercalate noticeLines

/-! ## Text -/

/-- Runs of white space collapsed to one space, and both ends trimmed. -/
def collapse (s : String) : String :=
  let flat := s.map fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c
  " ".intercalate ((flat.splitOn " ").filter (· != ""))

/-- A comma-separated list: each item collapsed, an empty item dropped. -/
def listOf (s : String) : List String :=
  ((s.splitOn ",").map collapse).filter (· != "")

/-- `href` resolved against the directory `master`, with each `..` applied. -/
def resolve (href : String) : String :=
  let parts := ("master/" ++ href).splitOn "/"
  let kept := parts.foldl (init := ([] : List String)) fun acc part =>
    if part == ".." then acc.dropLast
    else if part == "." || part == "" then acc
    else acc ++ [part]
  "/".intercalate kept

/-! ## Rows -/

/-- One `attribute` entry. `elements` is the entry's own list, which only an entry outside an
element and a category carries. -/
structure AttrDecl where
  name : String
  anchor : String
  animatable : String
  elements : List String
  deriving Inhabited

/-- One `element` entry. `kind` is the stated content model, or `prose` when the entry gives a
sentence; `sentence` is that sentence. `digest` is the SHA-256 of the entry's bytes. -/
structure ElementDecl where
  file : String
  name : String
  anchor : String
  kind : String
  sentence : String
  categories : List String
  elements : List String
  attrCategories : List String
  geometry : List String
  attributes : List String
  own : List AttrDecl
  digest : String
  deriving Inhabited

/-- One `elementcategory` entry. -/
structure CategoryDecl where
  file : String
  name : String
  anchor : String
  members : List String
  digest : String
  deriving Inhabited

/-- One `attributecategory` entry: the attributes it nests, and its presentation attributes. -/
structure AttrCategoryDecl where
  file : String
  name : String
  anchor : String
  own : List AttrDecl
  presentation : List String
  digest : String
  deriving Inhabited

/-- One `attribute` entry that stands outside an element and a category. -/
structure StandaloneDecl where
  file : String
  decl : AttrDecl
  digest : String
  deriving Inhabited

/-- Every entry the projection reads, in file order, and the names of the `property` entries. -/
structure Definitions where
  elements : List ElementDecl := []
  categories : List CategoryDecl := []
  attrCategories : List AttrCategoryDecl := []
  standalone : List StandaloneDecl := []
  properties : List String := []
  deriving Inhabited

/-- A name that an entry cites and no entry declares. -/
structure Dangling where
  citedAs : String
  name : String
  citedBy : List String
  deriving Inhabited

/-! ## Reading an entry -/

/-- The XML attributes an entry of each kind may carry. -/
def allowedKeys : String → List String
  | "element" =>
    ["name", "href", "contentmodel", "elementcategories", "elements", "attributecategories",
     "geometryproperties", "attributes", "interfaces"]
  | "elementcategory" => ["name", "href", "elements"]
  | "attributecategory" => ["name", "href", "presentationattributes"]
  | "attribute" =>
    ["name", "href", "animatable", "elements", "presentationattribute", "presentationattributehref"]
  | _ => []

/-- The stated content model kinds. -/
def statedKinds : List String := ["anyof", "any", "text", "textoranyof"]

/-- Where a node stands, for a refusal. -/
def place (node : Node) : String :=
  match node.span? with
  | some (start, _) => s!"offset {start}"
  | none => "character data"

/-- Refuse an XML attribute the entry's kind does not list, and an entry with no name. -/
def checkEntry (file kind : String) (node : Node) : Except String String := do
  for key in node.attrNames do
    unless (allowedKeys kind).contains key do
      throw s!"{file}: {place node}: the `{kind}` entry carries the unread attribute `{key}`"
  let name := node.attr "name"
  if name.isEmpty then
    throw s!"{file}: {place node}: a `{kind}` entry has no name"
  return name

/-- Refuse character data that is not white space, and a child element outside `allowed`. -/
def checkChildren (file : String) (allowed : List String) (node : Node) : Except String Unit := do
  for child in node.children do
    match child.name? with
    | none =>
      unless (collapse child.textContent).isEmpty do
        throw s!"{file}: {place node}: character data inside the entry `{node.attr "name"}`"
    | some name =>
      unless allowed.contains name do
        throw s!"{file}: {place child}: the unread element `{name}` inside the entry `{node.attr "name"}`"

def readAttr (file : String) (node : Node) : Except String AttrDecl := do
  let name ← checkEntry file "attribute" node
  checkChildren file [] node
  return { name, anchor := node.attr "href", animatable := node.attr "animatable",
           elements := listOf (node.attr "elements") }

def readElement (file digest : String) (node : Node) : Except String ElementDecl := do
  let name ← checkEntry file "element" node
  checkChildren file ["attribute", "x:contentmodel"] node
  let (kind, sentence) ←
    match node.attr? "contentmodel", node.childrenNamed "x:contentmodel" with
    | some stated, [] =>
      if statedKinds.contains stated then pure (stated, "")
      else throw s!"{file}: the element `{name}` states the unread content model `{stated}`"
    | none, [prose] => pure ("prose", collapse prose.textContent)
    | none, [] => throw s!"{file}: the element `{name}` has no content model"
    | _, _ => throw s!"{file}: the element `{name}` has two content models"
  let own ← (node.childrenNamed "attribute").mapM (readAttr file)
  return {
    file, name, anchor := node.attr "href", kind, sentence
    categories := listOf (node.attr "elementcategories")
    elements := listOf (node.attr "elements")
    attrCategories := listOf (node.attr "attributecategories")
    geometry := listOf (node.attr "geometryproperties")
    attributes := listOf (node.attr "attributes")
    own, digest }

def readCategory (file digest : String) (node : Node) : Except String CategoryDecl := do
  let name ← checkEntry file "elementcategory" node
  checkChildren file [] node
  return { file, name, anchor := node.attr "href", members := listOf (node.attr "elements"), digest }

def readAttrCategory (file digest : String) (node : Node) : Except String AttrCategoryDecl := do
  let name ← checkEntry file "attributecategory" node
  checkChildren file ["attribute"] node
  let own ← (node.childrenNamed "attribute").mapM (readAttr file)
  return { file, name, anchor := node.attr "href", own,
           presentation := listOf (node.attr "presentationattributes"), digest }

/-- The entry kinds that the projection counts and does not read. -/
def unreadKinds : List String := ["property", "term", "symbol", "interface"]

/-- A sealed file as a read document. The reader refuses a character outside ASCII, so the
offsets of its answer are offsets into `bytes`. -/
def readDocument (file : String) (bytes : ByteArray) : Except String Node := do
  let some text := String.fromUTF8? bytes
    | throw s!"{file}: the bytes are not UTF-8"
  match Gates.Xml.read text with
  | .ok root => return root
  | .error e => throw s!"{file}: {e}"

/-- Add one definitions file's entries. An entry's digest is the SHA-256 of its bytes. -/
def readFile (file : String) (bytes : ByteArray) (acc : Definitions) : Except String Definitions := do
  let root ← readDocument file bytes
  unless root.name? == some "definitions" do
    throw s!"{file}: the root element is not `definitions`"
  let mut defs := acc
  for child in root.children do
    match child with
    | .text content =>
      unless (collapse content).isEmpty do
        throw s!"{file}: character data between entries"
    | .element kind _ _ start stop =>
      let digest := Gates.Sha256.hexDigest (bytes.extract start stop)
      if kind == "element" then
        defs := { defs with elements := defs.elements ++ [← readElement file digest child] }
      else if kind == "elementcategory" then
        defs := { defs with categories := defs.categories ++ [← readCategory file digest child] }
      else if kind == "attributecategory" then
        defs := { defs with attrCategories := defs.attrCategories ++ [← readAttrCategory file digest child] }
      else if kind == "attribute" then
        defs := { defs with standalone := defs.standalone ++ [{ file, decl := ← readAttr file child, digest }] }
      else if kind == "property" then
        defs := { defs with properties := defs.properties ++ [child.attr "name"] }
      else if unreadKinds.contains kind then
        pure ()
      else
        throw s!"{file}: offset {start}: the unread entry kind `{kind}`"
  return defs

/-- The definitions files that `master/publish.xml` lists, resolved under the pin directory. -/
def listedFiles (publishBytes : ByteArray) : Except String (List String) := do
  let root ← readDocument publish.relative publishBytes
  return (root.childrenNamed "definitions").map fun node => resolve (node.attr "href")

/-! ## Dangling names -/

/-- The cited names that `declared` lacks, in the order first cited, each with its citers. -/
def danglingOf (citedAs : String) (declared : List String) (citations : List (String × String)) :
    List Dangling :=
  let names := (citations.map (·.1)).eraseDups.filter fun name => !declared.contains name
  names.map fun name =>
    { citedAs, name, citedBy := ((citations.filter (·.1 == name)).map (·.2)).eraseDups }

/-- Every dangling name, by what it is cited as: an element, an element category, an attribute
category, an attribute, a property. -/
def dangling (d : Definitions) : List Dangling :=
  let elementNames := d.elements.map (·.name)
  let elementCitations :=
    (d.elements.flatMap fun e => e.elements.map fun n => (n, e.name)) ++
    (d.categories.flatMap fun c => c.members.map fun n => (n, "category " ++ c.name)) ++
    (d.standalone.flatMap fun s => s.decl.elements.map fun n => (n, "attribute " ++ s.decl.name))
  let propertyCitations :=
    (d.attrCategories.flatMap fun c => c.presentation.map fun n => (n, "category " ++ c.name)) ++
    (d.elements.flatMap fun e => e.geometry.map fun n => (n, e.name))
  danglingOf "element" elementNames elementCitations ++
  danglingOf "element category" (d.categories.map (·.name))
    (d.elements.flatMap fun e => e.categories.map fun n => (n, e.name)) ++
  danglingOf "attribute category" (d.attrCategories.map (·.name))
    (d.elements.flatMap fun e => e.attrCategories.map fun n => (n, e.name)) ++
  danglingOf "attribute" (d.standalone.map (·.decl.name))
    (d.elements.flatMap fun e => e.attributes.map fun n => (n, e.name)) ++
  danglingOf "property" d.properties propertyCitations

/-! ## Outputs -/

def field (xs : List String) : String := ", ".intercalate xs

/-- The two header lines every projection opens with, before its column line. -/
def tsvHeader (name : String) (rows : Nat) : String :=
  s!"#{name} format=1 generator=Gates.SvgDefinitions inputs={pinDirectory} rows={rows} " ++
  "regenerate=lake exe whatwg_svgdefinitions --write\n" ++
  s!"#notice {notice}\n"

def elementsTsv (d : Definitions) : String :=
  tsvHeader "svg-elements" d.elements.length ++
  "#element\tfile\tanchor\tkind\tsentence\telement-categories\telements\tattribute-categories\t" ++
  "geometry-properties\tattributes\town-attributes\tspan-sha256\n" ++
  String.join (d.elements.map fun e =>
    "\t".intercalate [e.name, e.file, e.anchor, e.kind, e.sentence, field e.categories,
      field e.elements, field e.attrCategories, field e.geometry, field e.attributes,
      field (e.own.map (·.name)), e.digest] ++ "\n")

def categoriesTsv (d : Definitions) : String :=
  tsvHeader "svg-categories" (d.categories.length + d.attrCategories.length) ++
  "#kind\tcategory\tfile\tanchor\tmembers\tpresentation-attributes\tspan-sha256\n" ++
  String.join (d.categories.map fun c =>
    "\t".intercalate ["element", c.name, c.file, c.anchor, field c.members, "", c.digest] ++ "\n") ++
  String.join (d.attrCategories.map fun c =>
    "\t".intercalate ["attribute", c.name, c.file, c.anchor, field (c.own.map (·.name)),
      field c.presentation, c.digest] ++ "\n")

/-- One row of the attribute projection: the owner's kind and name, then the entry. -/
def attributeRows (d : Definitions) : List (List String) :=
  (d.elements.flatMap fun e => e.own.map fun a =>
    ["element", e.name, a.name, a.animatable, "", a.anchor]) ++
  (d.attrCategories.flatMap fun c => c.own.map fun a =>
    ["category", c.name, a.name, a.animatable, "", a.anchor]) ++
  (d.standalone.map fun s =>
    ["standalone", "-", s.decl.name, s.decl.animatable, field s.decl.elements, s.decl.anchor])

def attributesTsv (d : Definitions) : String :=
  let rows := attributeRows d
  tsvHeader "svg-attributes" rows.length ++
  "#owner-kind\towner\tattribute\tanimatable\telements\tanchor\n" ++
  String.join (rows.map fun row => "\t".intercalate row ++ "\n")

def danglingTsv (d : Definitions) : String :=
  let rows := dangling d
  tsvHeader "svg-dangling" rows.length ++
  "#cited-as\tname\tcited-by\n" ++
  String.join (rows.map fun r => "\t".intercalate [r.citedAs, r.name, field r.citedBy] ++ "\n")

/-- The projections: each path under the repository root, with its text. -/
def projections (d : Definitions) : List (String × String) :=
  [("generated/svg-elements.tsv", elementsTsv d),
   ("generated/svg-categories.tsv", categoriesTsv d),
   ("generated/svg-attributes.tsv", attributesTsv d),
   ("generated/svg-dangling.tsv", danglingTsv d)]

/-! ## Driver -/

/-- Read one sealed file, and refuse a digest that is not the pinned one. -/
def readPinned (root : System.FilePath) (input : Input) : IO ByteArray := do
  let relative := pinDirectory ++ "/" ++ input.relative
  let path := root / relative
  unless ← path.pathExists do
    throw <| IO.userError s!"svg definitions: missing input {relative}"
  let bytes ← IO.FS.readBinFile path
  let digest := Gates.Sha256.hexDigest bytes
  unless digest == input.digest do
    throw <| IO.userError
      s!"svg definitions: {relative} has digest {digest}, expected the pinned {input.digest}; re-pin before regenerating"
  return bytes

def liftExcept {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw <| IO.userError s!"svg definitions: {e}"

/-- Read the pin: the list of `master/publish.xml` must be the pinned list, file for file. -/
def load (root : System.FilePath) : IO Definitions := do
  let publishBytes ← readPinned root publish
  let listed ← liftExcept (listedFiles publishBytes)
  let pinned := definitionFiles.map (·.relative)
  unless listed == pinned do
    throw <| IO.userError
      s!"svg definitions: {publish.relative} lists {listed}, and the pinned definitions files are {pinned}"
  let mut defs : Definitions := {}
  for input in definitionFiles do
    defs ← liftExcept (readFile input.relative (← readPinned root input) defs)
  return defs

def summarize (d : Definitions) : String :=
  s!"svg definitions: {d.elements.length} elements, {d.categories.length} element categories, " ++
  s!"{d.attrCategories.length} attribute categories, {d.standalone.length} attributes outside an " ++
  s!"element or a category, {d.properties.length} properties and {(dangling d).length} dangling " ++
  s!"names from {definitionFiles.length} files of {pinDirectory}\n"

/-- The drift of committed files against fresh text: nothing when every file is identical. The
first ten differing lines of a file are shown. -/
def driftOf (root : System.FilePath) (files : List (String × String)) : IO (List String) := do
  let mut failures : List String := []
  for (relative, fresh) in files do
    let path := root / relative
    unless ← path.pathExists do
      failures := failures ++ [s!"missing {relative}; run `lake exe whatwg_svgdefinitions --write`"]
      continue
    let committed ← IO.FS.readFile path
    if committed != fresh then
      let expected := lines fresh
      let actual := lines committed
      failures := failures ++
        [s!"drift in {relative} ({actual.length} committed lines, {expected.length} regenerated)"]
      let mut shown := 0
      for (e, a) in expected.zip actual do
        if e != a && shown < 10 then
          failures := failures ++ [s!"  regenerated: {e}", s!"  committed:   {a}"]
          shown := shown + 1
  return failures

def writeFiles (root : System.FilePath) (files : List (String × String)) : IO Unit := do
  for (relative, text) in files do
    let path := root / relative
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path text
    IO.println s!"WROTE {relative}"

end Gates.SvgDefinitions
