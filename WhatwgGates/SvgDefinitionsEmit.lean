import WhatwgGates.SvgDefinitions
import WhatwgGates.EmitLean
import Whatwg.Svg.Schema.Readings

/-!
# Gates.SvgDefinitionsEmit

The SVG schema as generated Lean (slices S2 and S3a of `docs/SVG-PACKAGE-PLAN.md`). `build`
resolves the rows of `Gates.SvgDefinitions` into a schema, and four emitters write it:

- `Whatwg/Svg/Schema/Tags.lean`: `Tag`, its census, its spellings, and the guess of a name;
- `Whatwg/Svg/Schema/Categories.lean`: the element categories and each one's members;
- `Whatwg/Svg/Schema/Attributes.lean`: `Attr`, the attribute categories, and each tag's
  attributes;
- `Whatwg/Svg/Schema/ContentModel.lean`: each tag's content model.

Every set is a mask over its census (ruling SV-22): bit `i` is the census's name `i`. The
generator computes each resolution, and the library holds its value: a model's `tags` beside
its stated categories and elements, and a tag's `attrs` beside its own attributes and its
attribute categories. `Whatwg/Svg/Schema/Universe.lean` proves each resolved value equal to
the join of what is stated.

Resolution follows ruling SV-3. A dangling name is in no set: a dangling element is no child,
a dangling category has no member, and a dangling attribute is no attribute. Two entries that
declare one attribute category are merged.

An attribute reaches an element in five ways. Four make `Tag.ownAttrs`: the element nests it;
the element cites it; it stands outside every element and lists the element; the element lists
it as a geometry property. The fifth is an attribute category, `Tag.attrCategories`.

The four content models that the definitions state as a sentence come from the authored
`Whatwg/Svg/Schema/Readings.lean`. `build` refuses a reading whose sentence or digest is not
the entry's, a sentence with no reading, and a reading with no sentence.

`cli` is the gate `lake exe whatwg_svgdefinitions`: it checks, or with `--write` writes, the
four projections and the four modules.
-/

namespace Gates.SvgDefinitionsEmit

open Gates.Common Gates.SvgDefinitions Gates.EmitLean
open Whatwg.Svg.Schema.Readings (Reading readings)

/-! ## Lean spelling -/

/-- A definitions name as `ctorName` takes it: `:` and a space become `_`. -/
def spell (name : String) : String := (name.replace ":" "_").replace " " "_"

/-- A constructor in dot notation. -/
def ref (name : String) : String := "." ++ ctorName (spell name)

/-- A set over a census as a `Mask` literal: bit `i` is set when the census's name `i` is a
member. A member outside the census sets no bit. -/
def maskLiteral (census members : List String) : String :=
  let bits := census.zipIdx.foldl
    (fun acc (name, i) => if members.contains name then acc ||| (1 <<< i) else acc) 0
  "⟨0x" ++ String.ofList (Nat.toDigits 16 bits) ++ "⟩"

/-- A function from an enumeration to a mask over a census, one arm per row. -/
def emitMaskFn (fn doc domain codomain : String) (census : List String)
    (rows : List (String × List String)) : String :=
  let arms := rows.map fun (name, items) => s!"  | {ref name} => {maskLiteral census items}"
  s!"/-- {doc} -/\ndef {fn} : {domain} → Mask {codomain}\n" ++ "\n".intercalate arms ++ "\n\n"

/-- The spelling of each value of an enumeration, as characters. -/
def emitChars (domain doc : String) (names : List String) : String :=
  s!"/-- {doc} -/\ndef {domain}.chars : {domain} → List Char\n" ++
  "\n".intercalate (names.map fun name => s!"  | {ref name} => {charsPattern name}") ++ "\n\n"

/-- The guess of the value that a spelling names: a `List Char` match, which compiles to a
character decision tree. `NameTable.read` checks its answer. -/
def emitGuess (domain doc : String) (names : List String) : String :=
  s!"/-- {doc} -/\ndef {domain}.guess : List Char → Option {domain}\n" ++
  "\n".intercalate (names.map fun name => s!"  | {charsPattern name} => some {ref name}") ++
  "\n  | _ => none\n\n"

/-! ## The schema -/

/-- One tag's content model, resolved. `kind` is a constructor of the generated `ContentKind`. -/
structure ModelOut where
  kind : String
  categories : List String
  elements : List String
  children : List String
  text : Bool := false
  inherits : Bool := false
  through : List String := []
  excluded : List String := []
  bounds : List (List String × Nat × Nat) := []
  authored : Bool := false

/-- The resolved schema: every list holds declared names only. -/
structure Schema where
  defs : Definitions
  tags : List String
  categories : List (String × List String)
  attrs : List String
  attrCategories : List (String × List String)
  tagAttrCategories : List (String × List String)
  tagOwnAttrs : List (String × List String)
  tagAttrs : List (String × List String)
  models : List (String × ModelOut)
  handsOn : List String

/-- Refuse a list of names in which two spell one Lean constructor. -/
def distinct (what : String) (names : List String) : Except String Unit := do
  let spelled := names.map fun name => ctorName (spell name)
  unless spelled.eraseDups.length == spelled.length do
    throw s!"two {what} names spell one Lean constructor"

/-- The reading of a sentence, checked against the entry it reads. -/
def readingFor (e : ElementDecl) : Except String Reading := do
  match readings.filter (·.element == e.name) with
  | [reading] =>
    unless reading.sentence == e.sentence do
      throw s!"the reading of `{e.name}` reads another sentence than the entry's: {e.sentence}"
    unless reading.digest == e.digest do
      throw s!"the reading of `{e.name}` is pinned to another digest than the entry's {e.digest}; read the sentence again"
    return reading
  | [] => throw s!"the element `{e.name}` states its content model as a sentence, and no reading reads it"
  | _ => throw s!"the element `{e.name}` has two readings"

def build (d : Definitions) : Except String Schema := do
  let tags := d.elements.map (·.name)
  unless tags.eraseDups.length == tags.length do throw "an element is declared twice"
  let categoryNames := d.categories.map (·.name)
  unless categoryNames.eraseDups.length == categoryNames.length do
    throw "an element category is declared twice"
  let categories := d.categories.map fun c => (c.name, c.members.filter tags.contains)
  let membersOf (names : List String) : List String :=
    (categories.filter fun c => names.contains c.1).flatMap (·.2)
  -- attributes: a dangling name is no attribute
  let standaloneNames := d.standalone.map (·.decl.name)
  let attrCategoryNames := (d.attrCategories.map (·.name)).eraseDups
  let attrCategories := attrCategoryNames.map fun name =>
    (name, ((d.attrCategories.filter (·.name == name)).flatMap fun c =>
      c.own.map (·.name) ++ c.presentation.filter d.properties.contains).eraseDups)
  let ownOf (e : ElementDecl) : List String :=
    (e.own.map (·.name) ++ e.attributes.filter standaloneNames.contains ++
      e.geometry.filter d.properties.contains ++
      ((d.standalone.filter fun s => s.decl.elements.contains e.name).map (·.decl.name))).eraseDups
  let tagOwnAttrs := d.elements.map fun e => (e.name, ownOf e)
  let attrs := (tagOwnAttrs.flatMap (·.2) ++ attrCategories.flatMap (·.2) ++ standaloneNames).eraseDups
  let tagAttrCategories := d.elements.map fun e =>
    (e.name, e.attrCategories.filter attrCategoryNames.contains)
  -- content models
  for reading in readings do
    unless d.elements.any (fun e => e.name == reading.element && e.kind == "prose") do
      throw s!"the reading of `{reading.element}` reads no sentence of the definitions"
  let mut models : List (String × ModelOut) := []
  for e in d.elements do
    let resolve (cats els : List String) : List String :=
      let named := membersOf cats ++ els
      tags.filter named.contains
    if e.kind == "prose" then
      let reading ← readingFor e
      for name in reading.categories ++ reading.bounds.flatMap (·.categories) do
        unless categoryNames.contains name do
          throw s!"the reading of `{e.name}` names the undeclared category `{name}`"
      for name in reading.elements ++ reading.through ++ reading.excluded ++
          reading.bounds.flatMap (·.elements) do
        unless tags.contains name do
          throw s!"the reading of `{e.name}` names the undeclared element `{name}`"
      models := models ++ [(e.name, {
        kind := "anyOf", categories := reading.categories, elements := reading.elements
        children := resolve reading.categories reading.elements
        inherits := reading.inherits, through := reading.through, excluded := reading.excluded
        bounds := reading.bounds.map fun b => (resolve b.categories b.elements, b.atLeast, b.atMost)
        authored := true })]
    else
      let cats := e.categories.filter categoryNames.contains
      let els := e.elements.filter tags.contains
      let kind :=
        if e.kind == "anyof" then "anyOf"
        else if e.kind == "textoranyof" then "textOrAnyOf"
        else e.kind
      let named := e.kind == "anyof" || e.kind == "textoranyof"
      models := models ++ [(e.name, {
        kind, categories := if named then cats else [], elements := if named then els else []
        children := if named then resolve cats els else if e.kind == "any" then tags else []
        text := e.kind != "anyof" })]
  -- one set of elements hands on the outer model: two readings may not name different sets
  let inheriting := models.filter (·.2.inherits)
  let handsOn := (inheriting.map (·.2.through)).head?.getD []
  unless inheriting.all (fun m => m.2.through == handsOn) do
    throw "two readings inherit a parent's content model through different sets of elements"
  unless (models.filter (!·.2.inherits)).all (·.2.through.isEmpty) do
    throw "a reading names a set of elements to inherit through, and does not inherit"
  let tagAttrs := tagOwnAttrs.map fun (tag, own) =>
    let cited := (tagAttrCategories.find? (·.1 == tag)).map (·.2) |>.getD []
    (tag, own ++ (attrCategories.filter fun c => cited.contains c.1).flatMap (·.2))
  distinct "element" tags
  distinct "element category" categoryNames
  distinct "attribute" attrs
  distinct "attribute category" attrCategoryNames
  return { defs := d, tags, categories, attrs, attrCategories, tagAttrCategories, tagOwnAttrs, tagAttrs,
           models, handsOn }

/-! ## Emission -/

def header (moduleName summary : String) (imports : List String := []) : String :=
  String.join (imports.map fun m => s!"import {m}\n") ++ (if imports.isEmpty then "" else "\n") ++
  s!"/-!\n# {moduleName}\n\n{summary}\n\n" ++
  "GENERATED by `lake exe whatwg_svgdefinitions --write` from the sealed SVG 2 definitions\n" ++
  s!"under `{pinDirectory}/`, through the projections `generated/svg-*.tsv`.\n" ++
  "DO NOT EDIT: `lake exe whatwg_svgdefinitions` fails on any byte of drift. Slices S2 and S3a\n" ++
  "of `docs/SVG-PACKAGE-PLAN.md`; the generator is `WhatwgGates/SvgDefinitionsEmit.lean`.\n" ++
  "Data and derived instances only: no proof lives here. A set is a mask over its census;\n" ++
  "`generated/svg-*.tsv` lists each set by name, and `Mask.toList` reads a mask back.\n\n" ++
  "\n".intercalate noticeLines ++ "\n-/\n\n"

def emitTags (s : Schema) : String :=
  header "Whatwg.Svg.Schema.Tags"
    "The element universe of SVG 2: every element that the definitions declare at the pin, in\nthe order of the definitions files." ++
  "namespace Whatwg.Svg.Schema\n\n" ++
  emitEnum "Tag" "An element of SVG 2." (s.tags.map spell) ++
  emitAll "Tag.all" "Every tag, in the order of the definitions files." "Tag" (s.tags.map spell) ++
  emitChars "Tag" "The element's name, as a document writes it." s.tags ++
  emitGuess "Tag"
    "A guess of the tag that a spelling names. `Tag.ofChars?` checks it against `Tag.chars`."
    s.tags ++
  "end Whatwg.Svg.Schema\n"

def emitCategories (s : Schema) : String :=
  let names := s.categories.map (·.1)
  header "Whatwg.Svg.Schema.Categories"
    "The element categories of SVG 2, and the elements of each. A member that no definition\ndeclares is dropped: `generated/svg-dangling.tsv` lists it."
    ["Whatwg.Svg.Data.Mask", "Whatwg.Svg.Schema.Tags"] ++
  "namespace Whatwg.Svg.Schema\n\nopen Whatwg.Svg.Data (Mask)\n\n" ++
  emitEnum "Category" "An element category of SVG 2." (names.map spell) ++
  emitAll "Category.all" "Every element category, in the order of the definitions files." "Category"
    (names.map spell) ++
  emitStringFn "Category.name" "The category's name, as the definitions spell it." "Category"
    (names.map fun n => (spell n, n)) ++
  emitMaskFn "Category.members" "The elements of the category." "Category" "Tag" s.tags s.categories ++
  "end Whatwg.Svg.Schema\n"

def emitAttributes (s : Schema) : String :=
  let categoryNames := s.attrCategories.map (·.1)
  header "Whatwg.Svg.Schema.Attributes"
    "The attribute names of SVG 2, the attribute categories, and each element's attributes.\nAn attribute is a name: one name may take different values on different elements. An\nelement's attributes are `Tag.attrs`: its `Tag.ownAttrs` and the members of its\n`Tag.attrCategories`."
    ["Whatwg.Svg.Data.Mask", "Whatwg.Svg.Schema.Tags"] ++
  "namespace Whatwg.Svg.Schema\n\nopen Whatwg.Svg.Data (Mask)\n\n" ++
  emitEnum "Attr" "An attribute name of SVG 2." (s.attrs.map spell) ++
  emitAll "Attr.all" "Every attribute name, in the order first declared." "Attr" (s.attrs.map spell) ++
  emitChars "Attr" "The attribute's name, as a document writes it." s.attrs ++
  emitGuess "Attr"
    "A guess of the attribute that a spelling names. `Attr.ofChars?` checks it against\n`Attr.chars`."
    s.attrs ++
  emitEnum "AttrCategory" "An attribute category of SVG 2." (categoryNames.map spell) ++
  emitAll "AttrCategory.all" "Every attribute category, in the order first declared." "AttrCategory"
    (categoryNames.map spell) ++
  emitStringFn "AttrCategory.name" "The category's name, as the definitions spell it." "AttrCategory"
    (categoryNames.map fun n => (spell n, n)) ++
  emitMaskFn "AttrCategory.members"
    "The attributes of the category: those its entries nest, and its presentation attributes.\nTwo entries that declare one category are merged."
    "AttrCategory" "Attr" s.attrs s.attrCategories ++
  emitMaskFn "Tag.attrCategories" "The attribute categories that the element's entry cites."
    "Tag" "AttrCategory" categoryNames s.tagAttrCategories ++
  emitMaskFn "Tag.ownAttrs"
    "The attributes of the element outside its categories: those its entry nests or cites, its\ngeometry properties, and each attribute whose own entry lists the element."
    "Tag" "Attr" s.attrs s.tagOwnAttrs ++
  emitMaskFn "Tag.attrs"
    "The element's attributes, resolved: its own, and the members of its attribute categories."
    "Tag" "Attr" s.attrs s.tagAttrs ++
  "end Whatwg.Svg.Schema\n"

/-- One arm of `Tag.model`: a structure literal that omits each field at its default. -/
def modelArm (s : Schema) (name : String) (m : ModelOut) : String :=
  let categoryNames := s.categories.map (·.1)
  let line (label : String) (census items : List String) : List String :=
    if items.isEmpty then [] else [s!"      {label} := {maskLiteral census items}"]
  let bound (b : List String × Nat × Nat) : String :=
    "{ tags := " ++ maskLiteral s.tags b.1 ++ s!", atLeast := {b.2.1}, atMost := {b.2.2} " ++ "}"
  let fields :=
    line "categories" categoryNames m.categories ++ line "elements" s.tags m.elements ++
    line "tags" s.tags m.children ++
    (if m.text then ["      text := true"] else []) ++
    (if m.inherits then ["      inherits := true"] else []) ++
    line "excluded" s.tags m.excluded ++
    (if m.bounds.isEmpty then [] else
      ["      bounds := [" ++ ", ".intercalate (m.bounds.map bound) ++ "]"])
  s!"  | {ref name} =>\n    " ++ "{ " ++ s!"kind := .{m.kind}" ++
    String.join (fields.map fun f => "\n" ++ f) ++ " }"

def emitContentModel (s : Schema) : String :=
  header "Whatwg.Svg.Schema.ContentModel"
    "Each element's content model. The definitions state 59 of them by a kind and four by a\nsentence; a sentence's model is its reading in `Whatwg/Svg/Schema/Readings.lean`.\n`Model.tags` and `Model.text` are resolved: what the kind, the categories and the elements\nadmit together."
    ["Whatwg.Svg.Schema.Categories"] ++
  "namespace Whatwg.Svg.Schema\n\nopen Whatwg.Svg.Data (Mask)\n\n" ++
  "/-- How an element's content is stated: any number of the named elements; character data\nand those elements; character data alone; or any elements and character data. -/\n" ++
  "inductive ContentKind where\n  | anyOf | textOrAnyOf | text | any\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
  "/-- A bound that a sentence states: among an element's children, the elements of `tags`\nnumber at least `atLeast` and at most `atMost`. -/\n" ++
  "structure Bound where\n  tags : Mask Tag\n  atLeast : Nat\n  atMost : Nat\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
  "/-- One element's content model. `kind`, `categories` and `elements` are as stated. `tags`\nand `text` are resolved from them: the elements that may be children, and whether character\ndata may. With `inherits`, the model in force outside the element applies as well, and\n`excluded` names the elements that the model removes. Only a read sentence sets those two\nand `bounds`. -/\n" ++
  "structure Model where\n  kind : ContentKind\n  categories : Mask Category := ⟨0⟩\n  elements : Mask Tag := ⟨0⟩\n  tags : Mask Tag := ⟨0⟩\n  text : Bool := false\n  inherits : Bool := false\n  excluded : Mask Tag := ⟨0⟩\n  bounds : List Bound := []\n  deriving DecidableEq, Repr, Inhabited\n\n" ++
  "/-- The element's content model. -/\ndef Tag.model : Tag → Model\n" ++
  "\n".intercalate (s.models.map fun (name, m) => modelArm s name m) ++ "\n\n" ++
  "/-- The elements that hand on the model in force outside them: an inheriting child of one\nreads through it. Every reading that inherits names this one set. -/\n" ++
  s!"def handsOn : Mask Tag := {maskLiteral s.tags s.handsOn}\n\n" ++
  emitBoolSet "Tag.modelIsRead"
    "The elements whose content model is the reading of a sentence." "Tag"
    ((s.models.filter (·.2.authored)).map fun m => spell m.1) (s.tags.map spell) ++
  emitStringFn "Tag.digest"
    "The SHA-256 of the element's entry in its definitions file: the span digest of\n`generated/svg-elements.tsv`."
    "Tag" (s.defs.elements.map fun e => (spell e.name, e.digest)) ++
  "end Whatwg.Svg.Schema\n"
/-- The generated modules: each path under the repository root, with its text. -/
def modules (s : Schema) : List (String × String) :=
  [("Whatwg/Svg/Schema/Tags.lean", emitTags s),
   ("Whatwg/Svg/Schema/Categories.lean", emitCategories s),
   ("Whatwg/Svg/Schema/Attributes.lean", emitAttributes s),
   ("Whatwg/Svg/Schema/ContentModel.lean", emitContentModel s)]

/-! ## Driver -/

def summarize (s : Schema) : String :=
  s!"svg definitions emit: {s.tags.length} tags, {s.categories.length} element categories, " ++
  s!"{s.attrs.length} attribute names, {s.attrCategories.length} attribute categories, " ++
  s!"{(s.models.filter (·.2.authored)).length} content models read from a sentence\n"

/-- Every generated file, projections first. -/
def generate (root : System.FilePath) : IO (Definitions × Schema × List (String × String)) := do
  let defs ← load root
  let schema ← liftExcept (build defs)
  return (defs, schema, projections defs ++ modules schema)

def usage : String :=
  "usage: lake exe whatwg_svgdefinitions          check the four projections and the four schema modules against a regeneration\n" ++
  "       lake exe whatwg_svgdefinitions --write  regenerate all of them from the sealed SVG 2 definitions"

/-- Command-line entry, invoked by `whatwgbin/SvgDefinitions.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] =>
    let (defs, schema, files) ← generate root
    IO.print (Gates.SvgDefinitions.summarize defs)
    IO.print (summarize schema)
    let failures ← driftOf root files
    if failures.isEmpty then
      IO.println "PASS svg definitions: the four projections and the four schema modules are byte-identical to a fresh regeneration from the sealed definitions"
      return 0
    for failure in failures do IO.eprintln failure
    IO.eprintln "FAIL svg definitions"
    return 1
  | ["--write"] =>
    let (defs, schema, files) ← generate root
    writeFiles root files
    IO.print (Gates.SvgDefinitions.summarize defs)
    IO.print (summarize schema)
    return 0
  | _ =>
    IO.eprintln usage
    return 2

end Gates.SvgDefinitionsEmit
