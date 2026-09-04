import Gates.Common
import Gates.Sha256

/-!
# Gates.HtmlStandard

The HTML Standard's element definitions as a projection (slice H6 of
`docs/HTML-PACKAGE-PLAN.md`, rulings HP-1, HP-2 and HP-11): for every
`<dl class="element">` block of the sealed `source` at the pin, the element
names its heading defines and the `Categories`, `Contexts in which this
element can be used`, `Content model` and `Content attributes` entries as
plain text, with the SHA-256 of the bytes between the block's open tag and
its `</dl>` as the span digest every divergence row cites. Two outputs, both checked for byte drift:

- `generated/html-standard-elements.tsv`, one row per element name;
- `Whatwg/Html/Schema/Standard.lean`, the same rows as Lean data
  (`stdElements`), which `Whatwg.Html.Content.Fidelity` reads to state port
  fidelity against TyXML's projection.

The text is the standard's own words with markup removed, entities decoded
and whitespace collapsed; nothing is interpreted here. The reading of a
content-model sentence as a set is `Fidelity.classify`, in the semantic
tree, so that the interpretation is visible where it is used.

Totality: every scan is `String.splitOn` over the sealed text; no fuel, no
`partial`. The gate refuses a `source` whose digest is not the pinned one.
-/

namespace Gates.HtmlStandard

open Gates.Common

structure Input where
  relative : String
  digest : String

def source : Input :=
  { relative := "vendor/whatwg-html-746f2ede/source"
    digest := "c985a14d1871fe862de386f5af92b5da84068267c6095ef0379c069ae85f9cde" }

def projectionPath (root : System.FilePath) : System.FilePath :=
  root / "generated" / "html-standard-elements.tsv"

def modulePath (root : System.FilePath) : System.FilePath :=
  root / "Whatwg" / "Html" / "Schema" / "Standard.lean"

/-- One element row of the projection. -/
structure Row where
  name : String
  line : Nat
  digest : String
  categories : List String
  contexts : List String
  contentModel : List String
  attributes : List String
  deriving Repr, Inhabited

/-! ## Text -/

/-- Remove every `<...>` sequence, keeping the text between tags. -/
def stripTags (s : String) : String :=
  match s.splitOn "<" with
  | [] => ""
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      match piece.splitOn ">" with
      | [] => ""
      | _ :: after => ">".intercalate after)

/-- Decode the entities the source uses in these entries. -/
def unescape (s : String) : String :=
  ((((s.replace "&lt;" "<").replace "&gt;" ">").replace "&quot;" "\"").replace "&nbsp;" " ").replace "&amp;" "&"

/-- Collapse runs of whitespace to one space and trim. -/
def collapse (s : String) : String :=
  let flat := ((s.replace "\n" " ").replace "\t" " ").replace "\r" " "
  " ".intercalate ((flat.splitOn " ").filter (· != ""))

def clean (s : String) : String := collapse (unescape (stripTags s))

/-- The text up to the first occurrence of `stop`, or all of it. -/
def upTo (s stop : String) : String :=
  match s.splitOn stop with
  | [] => ""
  | first :: _ => first

/-- The `<dd>` entries under the `<dt>` whose `data-x` is
`concept-element-<key>`, as cleaned text. -/
def entries (block : String) (key : String) : List String :=
  let marker := "data-x=\"concept-element-" ++ key ++ "\""
  let dts := (block.splitOn "<dt>").drop 1
  match dts.find? (fun dt => ((upTo dt "</dt>").splitOn marker).length > 1) with
  | none => []
  | some dt =>
    let after := match dt.splitOn "</dt>" with | [] => "" | _ :: rest => "</dt>".intercalate rest
    ((after.splitOn "<dd").drop 1).filterMap fun dd =>
      let body := match (upTo dd "</dd>").splitOn ">" with | [] => "" | _ :: rest => ">".intercalate rest
      let text := clean body
      if text.isEmpty then none else some text

/-- The element names a heading defines: each `<dfn element>` of the last
`<h4>` before the block. -/
def headingNames (preceding : String) : List String :=
  match (preceding.splitOn "<h4").getLast? with
  | none => []
  | some h =>
    let heading := upTo h "</h4>"
    ((heading.splitOn "<dfn").drop 1).filterMap fun dfn =>
      -- the opening tag's attributes precede its first `>`; `element` must be
      -- one of them as a word (`<dfn element>`, `<dfn id="x" element>`)
      let openTag := " " ++ collapse (upTo dfn ">") ++ " "
      if (openTag.splitOn " element ").length < 2 then none else
      let body := match dfn.splitOn ">" with | [] => "" | _ :: rest => ">".intercalate rest
      let name := clean (upTo body "</dfn>")
      if name.isEmpty then none else some name

def countNewlines (s : String) : Nat := s.foldl (fun n c => if c == '\n' then n + 1 else n) 0

/-- Every row of the projection, in source order. The block opens as
`<dl class="element">` or, once (`menu`), as `<dl class=element>`; the
span digest is over the bytes strictly between the open tag and the
block's `</dl>`, which is the same span under either spelling. -/
def rowsOf (text : String) : List Row := Id.run do
  let open_ := "<dl class=\"element\">"
  let parts := (text.replace "<dl class=element>" open_).splitOn open_
  let mut rows : Array Row := #[]
  let mut line := 1
  let mut preceding := ""
  for i in [0:parts.length] do
    let part := parts[i]!
    if i > 0 then
      let body := upTo part "</dl>"
      let block := open_ ++ body ++ "</dl>"
      let digest := Gates.Sha256.hexDigestOfString body
      for name in headingNames preceding do
        rows := rows.push
          { name, line, digest
            categories := entries block "categories"
            contexts := entries block "contexts"
            contentModel := entries block "content-model"
            attributes := entries block "attributes" }
    line := line + countNewlines part
    preceding := part
  return rows.toList

/-! ## Outputs -/

def tsvHeader (rows : Nat) : String :=
  s!"#html-standard-elements format=1 generator=Gates.HtmlStandard inputs={source.relative} " ++
  s!"input-sha256={source.digest} rows={rows} regenerate=lake exe htmlstandard --write\n" ++
  "#element\tline\tspan-sha256\tcategories\tcontexts\tcontent-model\tattributes\n"

def field (xs : List String) : String := " | ".intercalate xs

def tsvRow (r : Row) : String :=
  "\t".intercalate [r.name, toString r.line, r.digest, field r.categories, field r.contexts,
    field r.contentModel, field r.attributes] ++ "\n"

def tsvOf (rows : List Row) : String := tsvHeader rows.length ++ String.join (rows.map tsvRow)

def leanList (xs : List String) : String := "[" ++ ", ".intercalate (xs.map String.quote) ++ "]"

def leanRow (r : Row) : String :=
  "   { name := " ++ r.name.quote ++ ", line := " ++ toString r.line ++ ",\n     digest := " ++ r.digest.quote ++
  ",\n     categories := " ++ leanList r.categories ++ ",\n     contexts := " ++ leanList r.contexts ++
  ",\n     contentModel := " ++ leanList r.contentModel ++ ",\n     attributes := " ++ leanList r.attributes ++ " }"

def moduleOf (rows : List Row) : String :=
  "/-!\n# Whatwg.Html.Schema.Standard\n\nThe HTML Standard's element definitions: for every element the standard\ndefines at the pin, its heading name, the line of its `<dl class=\"element\">`\nblock in `source`, the SHA-256 of the bytes between that block's open tag\nand its `</dl>` (the span digest every divergence row cites), and the `Categories`, `Contexts in which this element\ncan be used`, `Content model` and `Content attributes` entries as the\nstandard's own words with markup removed. Nothing here is interpreted; the\nreading of a content-model sentence as a set is\n`Whatwg.Html.Content.Fidelity.classify`.\n\nGENERATED by `lake exe htmlstandard --write` from the sealed HTML Standard\n`vendor/whatwg-html-746f2ede/source` (SHA-256 `" ++ source.digest ++ "`).\nDO NOT EDIT: `lake exe htmlstandard` fails on any byte of drift. Slice H6 of\n`docs/HTML-PACKAGE-PLAN.md`; the generator is `Gates/HtmlStandard.lean`.\nData only: no proof lives here.\n-/\n\nnamespace Whatwg.Html.Schema\n\n/-- One element definition of the HTML Standard, as its text. -/\nstructure StdElement where\n  name : String\n  line : Nat\n  digest : String\n  categories : List String\n  contexts : List String\n  contentModel : List String\n  attributes : List String\n  deriving Repr, Inhabited\n\n/-- Every element definition, in the order of `source`. -/\ndef stdElements : List StdElement :=\n  [" ++
  dropChars (",\n".intercalate (rows.map leanRow)) 3 ++ "]\n\nend Whatwg.Html.Schema\n"

/-! ## Driver -/

def readSource (root : System.FilePath) : IO String := do
  let path := root / source.relative
  unless ← path.pathExists do
    throw <| IO.userError s!"html standard: missing input {source.relative}"
  let bs ← IO.FS.readBinFile path
  let digest := Gates.Sha256.hexDigest bs
  unless digest == source.digest do
    throw <| IO.userError
      s!"html standard: {source.relative} has digest {digest}, expected the pinned {source.digest}; re-pin before regenerating"
  return String.fromUTF8! bs

structure Generated where
  rows : List Row
  tsv : String
  module : String

def generate (root : System.FilePath) : IO Generated := do
  let rows := rowsOf (← readSource root)
  return { rows, tsv := tsvOf rows, module := moduleOf rows }

def summarize (g : Generated) : String :=
  s!"html standard: {g.rows.length} element rows from {source.relative}\n"

def write (root : System.FilePath) : IO UInt32 := do
  let g ← generate root
  IO.FS.createDirAll (root / "generated")
  IO.FS.writeFile (projectionPath root) g.tsv
  IO.FS.writeFile (modulePath root) g.module
  IO.print (summarize g)
  IO.println s!"WROTE {← relativeTo root (projectionPath root)}"
  IO.println s!"WROTE {← relativeTo root (modulePath root)}"
  return 0

def check (root : System.FilePath) : IO UInt32 := do
  let g ← generate root
  let mut failures : List String := []
  for (path, fresh, what) in [(projectionPath root, g.tsv, "projection"), (modulePath root, g.module, "module")] do
    unless ← path.pathExists do
      failures := failures ++ [s!"missing {what} {← relativeTo root path}; run `lake exe htmlstandard --write`"]
      continue
    let committed ← IO.FS.readFile path
    if committed != fresh then
      let expected := lines fresh
      let actual := lines committed
      failures := failures ++ [s!"{what} drift in {← relativeTo root path} ({actual.length} committed lines, {expected.length} regenerated)"]
      let mut shown := 0
      for (e, a) in expected.zip actual do
        if e != a && shown < 10 then
          failures := failures ++ [s!"  regenerated: {e}", s!"  committed:   {a}"]
          shown := shown + 1
  IO.print (summarize g)
  if failures.isEmpty then
    IO.println "PASS html standard: generated/html-standard-elements.tsv and Whatwg/Html/Schema/Standard.lean are byte-identical to a fresh regeneration from the sealed source"
    return 0
  for f in failures do IO.eprintln f
  IO.eprintln "FAIL html standard"
  return 1

def usage : String :=
  "usage: lake exe htmlstandard          check the projection and the generated module against a regeneration\n" ++
  "       lake exe htmlstandard --write  regenerate both from the sealed HTML Standard source"

/-- Command-line entry, invoked by `bin/HtmlStandard.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] => check root
  | ["--write"] => write root
  | _ =>
    IO.eprintln usage
    return 2

end Gates.HtmlStandard
