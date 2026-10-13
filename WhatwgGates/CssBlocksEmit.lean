import WhatwgGates.CssBlocks

/-!
# Gates.CssBlocksEmit

Owner: the tables of slice K1 of `docs/CSS-PACKAGE-PLAN.md`, and the gate
`lake exe whatwg_cssblocks`.

`Gates.CssBlocks` reads the blocks of a sealed CSS module into rows. This module writes them:

- `generated/css/<module>-properties.tsv`, one row per property of a `propdef` block;
- `generated/css/<module>-descriptors.tsv`, one row per descriptor of a `descdef` block;
- `generated/css/<module>-productions.tsv`, one row per production;
- `generated/css/<module>-diagrams.tsv`, one row per railroad diagram;
- `generated/css/<module>-tables.tsv`, the headings and the marked cells of each table read;
- `generated/css/INDEX.tsv`, one row per sealed module, with its counts;
- `Whatwg/Css/Data/Pairs.lean`, the table of CSS Syntax 3 under `serialization-tables` as Lean
  data.

There is one file per kind per module, and a module with no block of a kind has no file of
that kind: sealing a module adds its files and its row of the index, and changes no other
file. Every row opens with the same seven cells: module, kind, name, the block's byte span,
the SHA-256 of the block's bytes, and the class of each `div` around the block. An empty cell
says that the block does not state the field. Rows stand in the order of the source.

`cli` checks every file for byte drift against a fresh regeneration, refuses a file under
`generated/css/` that no module accounts for, and runs the controls: sources with one
planted fault each, which the extractor must refuse for the stated reason.

The extractor is code that no theorem checks. A PASS is its verdict and no proof (ruling CS-3).
-/

namespace Gates.CssBlocksEmit

open Gates.Common Gates.CssBlocks

/-! ## Tables -/

/-- The directory of the tables, under the repository root. -/
def tablesDirectory : String := "generated/css"

/-- Where the table of pairs lands as Lean data. -/
def pairsPath : String := "Whatwg/Css/Data/Pairs.lean"

/-- The module and the anchor of the table that `pairsPath` holds. -/
def pairsSource : String × String := ("css-syntax-3", "serialization-tables")

/-- The statement that the W3C Software and Document License asks of a derived work, on one
line. The title is the module's own, from its metadata block. -/
def notice (e : Extract) : String :=
  "Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from " ++
  s!"{e.title}, https://drafts.csswg.org/{e.module.name}/, under the W3C Software and " ++
  "Document License, https://www.w3.org/copyright/software-license-2023/"

/-- A cell holds no tab and no line end. -/
def cell (s : String) : String :=
  s.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c

/-- One row: its cells between tabs, and a line end. -/
def row (cells : List String) : String := "\t".intercalate (cells.map cell) ++ "\n"

/-- The seven cells every row opens with. -/
def originCells (o : Origin) (name : String) : List String :=
  [o.module, o.kind, name, toString o.start, toString o.stop, o.digest, o.within]

/-- How many blocks of a kind the module holds. -/
def blockCount (e : Extract) (kind : String) : Nat :=
  ((e.blocks.find? (·.1 == kind)).map (·.2)).getD 0

/-- The three header lines of a table: what it is, the notice, the columns. -/
def tsvHeader (table : String) (e : Extract) (blocks rows : Nat) (columns : List String) : String :=
  s!"#css-{table} format=1 generator=Gates.CssBlocks module={e.module.name} " ++
  s!"input={e.module.path} input-sha256={e.module.digest} blocks={blocks} rows={rows} " ++
  "regenerate=lake exe whatwg_cssblocks --write\n" ++
  s!"#notice {notice e}\n" ++
  "#" ++ "\t".intercalate
    (["module", "kind", "name", "start", "end", "sha256", "within"] ++ columns) ++ "\n"

/-- A table of fields: the grammar line with Bikeshed's spelling undone, then one column for
each field of `known` but `Name`, as the block writes it. -/
def fieldsTsv (table : String) (known : List String) (e : Extract) (blocks : Nat)
    (rows : List FieldRow) : String :=
  let columns := known.filter (· != "Name")
  tsvHeader table e blocks rows.length ("grammar" :: columns) ++
  String.join (rows.map fun r =>
    row (originCells r.origin r.name ++ [r.grammar] ++
      columns.map fun c => (fieldOf r.fields c).getD ""))

/-- The productions: each one's place in its block, the `dfn` tag around its name, and its
right-hand side with Bikeshed's spelling undone. A row with no name is an expression. -/
def productionsTsv (e : Extract) : String :=
  tsvHeader "productions" e (blockCount e "prod" + blockCount e "pre") e.productions.length
    ["ordinal", "head", "rhs"] ++
  String.join (e.productions.map fun r =>
    row (originCells r.origin r.production.name ++
      [toString r.ordinal, r.production.head, r.production.rhs]))

/-- The diagrams: the `id` of the `dt` that names each, how many nodes it has, and its tree
on one line (`Gates.CssBlocks.printTree`). -/
def diagramsTsv (e : Extract) : String :=
  tsvHeader "diagrams" e (blockCount e "railroad") e.diagrams.length ["anchor", "nodes", "tree"] ++
  String.join (e.diagrams.map fun r =>
    row (originCells r.origin r.name ++ [r.anchor, toString r.nodes.length, printTree r.nodes]))

/-- The rows of one table: its column headings, its row headings, then its marked cells. -/
def tableRows (r : TableRow) : List (List String) :=
  r.table.columns.map (fun c => originCells r.origin r.anchor ++ ["column", "", c]) ++
  r.table.rows.map (fun name => originCells r.origin r.anchor ++ ["row", name, ""]) ++
  r.table.marked.map fun (name, c) => originCells r.origin r.anchor ++ ["pair", name, c]

/-- The tables read: a `column` row for each column heading, a `row` row for each row
heading, and a `pair` row for each marked cell. -/
def tablesTsv (e : Extract) : String :=
  let rows := e.tables.flatMap tableRows
  tsvHeader "tables" e e.tables.length rows.length ["cell", "row", "column"] ++
  String.join (rows.map row)

/-- The tables of one module: each path under the repository root, with its text. A kind
with no row has no file. -/
def moduleFiles (e : Extract) : List (String × String) :=
  let file (kind text : String) (rows : Nat) : List (String × String) :=
    if rows == 0 then [] else [(s!"{tablesDirectory}/{e.module.name}-{kind}.tsv", text)]
  file "properties"
    (fieldsTsv "properties" propertyFields e (blockCount e "propdef") e.properties)
    e.properties.length ++
  file "descriptors"
    (fieldsTsv "descriptors" descriptorFields e (blockCount e "descdef") e.descriptors)
    e.descriptors.length ++
  file "productions" (productionsTsv e) e.productions.length ++
  file "diagrams" (diagramsTsv e) e.diagrams.length ++
  file "tables" (tablesTsv e) e.tables.length

/-- One row per module: its title, its source and digest, its size, and how many blocks and
rows of each kind were read. A zero is a reading too. `passed-over` counts the opening tags
with a block class inside a comment or a `script`, `style` or `xmp` element: no row comes
from them, and the number says that they are there. -/
def indexTsv (es : List Extract) : String :=
  s!"#css-index format=1 generator=Gates.CssBlocks pin={pinDirectory} modules={es.length} " ++
  "regenerate=lake exe whatwg_cssblocks --write\n" ++
  "#" ++ "\t".intercalate ["module", "title", "input", "input-sha256", "bytes", "propdef-blocks",
    "property-rows", "descdef-blocks", "descriptor-rows", "prod-blocks", "pre-blocks",
    "production-rows", "railroad-blocks", "diagram-rows", "tables", "table-rows",
    "passed-over"] ++ "\n" ++
  String.join (es.map fun e =>
    row ([e.module.name, e.title, e.module.path, e.module.digest] ++
      ([e.size, blockCount e "propdef", e.properties.length, blockCount e "descdef",
        e.descriptors.length, blockCount e "prod", blockCount e "pre", e.productions.length,
        blockCount e "railroad", e.diagrams.length, e.tables.length,
        (e.tables.flatMap tableRows).length, e.passed].map toString)))

/-! ## The table of pairs as Lean data -/

/-- A Lean string literal. -/
def leanString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else String.singleton c) ++ "\""

/-- A Lean list literal, a few items to the line. -/
def leanList (items : List String) (perLine : Nat) : String :=
  let lines := Id.run do
    let mut out : List String := []
    let mut current : List String := []
    for item in items do
      current := current ++ [item]
      if current.length == perLine then
        out := out ++ [", ".intercalate current]
        current := []
    if !current.isEmpty then out := out ++ [", ".intercalate current]
    return out
  "[" ++ ",\n   ".intercalate lines ++ "]"

/-- The module `Whatwg.Css.Data.Pairs`. -/
def pairsLean (e : Extract) (r : TableRow) : String :=
  "/-!\n# Whatwg.Css.Data.Pairs\n\n" ++
  s!"The table of marks under the anchor `{r.anchor}` of\n{e.title}:\n" ++
  "the pairs of tokens that the standard says are written with a comment between them.\n" ++
  "`marked` holds one pair for each marked cell: the heading of its row, which stands for the\n" ++
  "first token, and the heading of its column, which stands for the second. `rows` and\n" ++
  "`columns` hold every heading in the table's order, so a pair of headings that is not in\n" ++
  "`marked` is a cell the table leaves empty.\n\n" ++
  "A heading is the table's own text. Which token a heading stands for is said by the note\n" ++
  "above the table, and not here: a reading of that note is authored, and it pins `digest`.\n\n" ++
  "GENERATED by `lake exe whatwg_cssblocks --write` from the sealed\n" ++
  s!"`{e.module.path}`, bytes {r.origin.start} to\n" ++
  s!"{r.origin.stop}, through the projection `{tablesDirectory}/{e.module.name}-tables.tsv`.\n" ++
  "DO NOT EDIT: `lake exe whatwg_cssblocks` fails on any byte of drift. Slice K1 of\n" ++
  "`docs/CSS-PACKAGE-PLAN.md`; the generator is `WhatwgGates/CssBlocksEmit.lean`.\n" ++
  "Data only: no proof lives here.\n\n" ++
  s!"Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from\n" ++
  s!"{e.title}, https://drafts.csswg.org/{e.module.name}/, under the W3C\n" ++
  "Software and Document License, https://www.w3.org/copyright/software-license-2023/\n-/\n\n" ++
  "namespace Whatwg.Css.Data.Pairs\n\n" ++
  "/-- The SHA-256 of the table's bytes in the sealed source. -/\n" ++
  s!"def digest : String :=\n  {leanString r.origin.digest}\n\n" ++
  "/-- The table's byte span in the sealed source: its first byte, and the byte after its\n" ++
  "last. -/\n" ++
  s!"def span : Nat × Nat := ({r.origin.start}, {r.origin.stop})\n\n" ++
  "/-- The row headings, in the table's order: each stands for the first token of a pair. -/\n" ++
  s!"def rows : List String :=\n  {leanList (r.table.rows.map leanString) 8}\n\n" ++
  "/-- The column headings, in the table's order: each stands for the second token of a\n" ++
  "pair. -/\n" ++
  s!"def columns : List String :=\n  {leanList (r.table.columns.map leanString) 8}\n\n" ++
  "/-- The marked cells, row by row: the heading of the row, then the heading of the\n" ++
  "column. -/\n" ++
  "def marked : List (String × String) :=\n  " ++
  leanList (r.table.marked.map fun (name, c) => s!"({leanString name}, {leanString c})") 4 ++
  "\n\n" ++
  "end Whatwg.Css.Data.Pairs\n"

/-- The module of pairs, when the module that holds the table is among those read. That
module must hold exactly one table under the anchor. -/
def pairsFile (es : List Extract) : Except String (List (String × String)) := do
  let some e := es.find? (·.module.name == pairsSource.1) | return []
  match e.tables.filter (·.anchor == pairsSource.2) with
  | [r] => return [(pairsPath, pairsLean e r)]
  | found =>
    throw (s!"{e.module.name}: {found.length} tables stand under `{pairsSource.2}`, and " ++
      s!"`{pairsPath}` holds one")

/-- Every generated file: the tables of each module, the index, the module of pairs. -/
def outputs (es : List Extract) : Except String (List (String × String)) := do
  return es.flatMap moduleFiles ++ [(s!"{tablesDirectory}/INDEX.tsv", indexTsv es)] ++
    (← pairsFile es)

/-! ## Controls -/

/-- A source that holds one block of every kind, a block inside a comment, and a table. -/
def plantedSource : String := "\n".intercalate [
  "<pre class='metadata'>",
  "Title: A Module of Controls",
  "</pre>",
  "<div class=example>",
  "<pre class=prod>",
  "<dfn>&lt;sample></dfn> = <<length>> |",
  "  <l>''auto''</l>",
  "&lt;other> = [ a | b ]#",
  "</pre>",
  "</div>",
  "<p>Prose with <<length>>, and a < b.",
  "<!-- <pre class='propdef'>",
  "Name: hidden",
  "</pre> -->",
  "<pre class=\"propdef\">",
  "Name: first, second",
  "Value: none | <<length>>",
  "Initial: none",
  "Inherited: no",
  "Computed value: a length,",
  "    made absolute",
  "</pre>",
  "<pre class='descdef mq'>",
  "\tName: wide",
  "\tFor: @media",
  "\tValue: <<length>>",
  "\tType: range",
  "\t</pre>",
  "<dl>",
  "<dt id=\"sample-diagram\"><<sample>>",
  "<dd>",
  "\t<pre class='railroad'>",
  "\tT: (",
  "\tChoice: 1",
  "\t\tN: a \"b\"",
  "\t\tS:",
  "\tOpt: skip",
  "\t\tStar:",
  "\t\t\tN: c",
  "\t</pre>",
  "</dl>",
  "<span class=prod><dfn>f()</dfn> = f( <<number>> )</span>",
  "<div id='marks'>",
  "<table>",
  "<tr><td><th>a<th>b",
  "<tr><th>x<td>" ++ mark ++ "<td> ",
  "<tr><th>y<td><td>" ++ mark,
  "</table>",
  "</div>",
  ""]

/-- What a reading says, without spans and digests: one line for each row. -/
def said (e : Extract) : List String :=
  [s!"title {e.title}", s!"passed over {e.passed}"] ++
  e.properties.map (fun r => s!"property {r.origin.kind} {r.name} := {r.grammar} " ++
    "; ".intercalate (r.fields.map fun (key, value) => s!"{key}={value}")) ++
  e.descriptors.map (fun r => s!"descriptor {r.origin.kind} {r.name} := {r.grammar} " ++
    "; ".intercalate (r.fields.map fun (key, value) => s!"{key}={value}")) ++
  e.productions.map (fun r => s!"production {r.origin.kind} [{r.origin.within}] {r.ordinal} " ++
    s!"{r.production.head} {r.production.name} = {r.production.rhs}") ++
  e.diagrams.map (fun r => s!"diagram {r.name} #{r.anchor} {printTree r.nodes}") ++
  e.tables.flatMap fun r =>
    [s!"table {r.anchor} columns {r.table.columns} rows {r.table.rows} marked {r.table.marked}"]

/-- What the planted source says. -/
def plantedSaid : List String :=
  ["title A Module of Controls",
   "passed over 1",
   "property propdef first := none | <length> Value=none | <<length>>; Initial=none; " ++
     "Inherited=no; Computed value=a length, made absolute",
   "property propdef second := none | <length> Value=none | <<length>>; Initial=none; " ++
     "Inherited=no; Computed value=a length, made absolute",
   "descriptor descdef mq wide := <length> For=@media; Value=<<length>>; Type=range",
   "production pre.prod [example] 1 <dfn> <sample> = <length> | auto",
   "production pre.prod [example] 2  <other> = [ a | b ]#",
   "production span.prod [] 1 <dfn> f() = f( <number> )",
   "diagram <sample> #sample-diagram (T \"(\") (Choice 1 (N \"a \\\"b\\\"\") (S)) " ++
     "(Opt skip (Star (N \"c\")))",
   "table marks columns [a, b] rows [x, y] marked [(x, a), (y, b)]"]

/-- What a control expects: the reading said in full, a number of property rows, or a
refusal whose message holds a text. -/
inductive Expect where
  | says (lines : List String)
  | properties (count : Nat)
  | refuses (fragment : String)

/-- One control: the planted source with one text replaced, the anchors of its tables, and
what the extractor must answer. -/
structure Control where
  label : String
  old : String
  new : String
  anchors : List String := ["marks"]
  expect : Expect

/-- The controls: the planted source as it is, and then one fault at a time. -/
def controls : List Control :=
  [{ label := "the planted source is read, and its block inside a comment is not",
     old := "", new := "", expect := .says plantedSaid },
   { label := "outside the comment, the hidden block is a third property",
     old := "<!-- <pre class='propdef'>\nName: hidden\n</pre> -->",
     new := "<pre class='propdef'>\nName: hidden\n</pre>", expect := .properties 3 },
   { label := "a field outside the list",
     old := "Inherited: no", new := "Inherited: no\nColour: red",
     expect := .refuses "the unread field `Colour`" },
   { label := "a field that stands twice",
     old := "Initial: none", new := "Initial: none\nInitial: 0",
     expect := .refuses "the field `Initial` stands twice" },
   { label := "a class beside `propdef` outside the list", old := "<pre class=\"propdef\">",
     new := "<pre class=\"propdef draft\">", expect := .refuses "the unread class `draft`" },
   { label := "an attribute on a block's opening tag", old := "<pre class=\"propdef\">",
     new := "<pre class=\"propdef\" data-x=1>",
     expect := .refuses "the unread attribute `data-x`" },
   { label := "a block with its closing tag missing, at the end of the source",
     old := "</table>\n</div>\n", new := "</table>\n</div>\n<pre class='railroad'>\nT: a\n",
     expect := .refuses "the `pre` element of a `railroad` block has no closing tag" },
   { label := "a block with its closing tag missing, before another block",
     old := "    made absolute\n</pre>", new := "    made absolute",
     expect := .refuses "a `pre` element opens inside a `propdef` block" },
   { label := "a block class on an element that is not read", old := "<span class=prod>",
     new := "<td class=prod>", expect := .refuses "the unread element `td` of class `prod`" },
   { label := "a block class inside a block: the walk does not see it, and the second scan does",
     old := "<l>''auto''</l>", new := "<l class=prod>''auto''</l>",
     expect := .refuses
       "7 opening tags carry a block class, and 5 were read as blocks and 1 passed over" },
   { label := "a diagram line that is not a whole number of steps in",
     old := "\t\tS:", new := "\t\t S:",
     expect := .refuses "is not indented by a whole number of steps" },
   { label := "a diagram line two steps deeper than the line above it", old := "\t\tStar:",
     new := "\t\t\tStar:", expect := .refuses "more than one step deeper" },
   { label := "a diagram line under a node that holds none",
     old := "\tT: (", new := "\tT: (\n\t\tN: d",
     expect := .refuses "stands under the node `T`, which holds none" },
   { label := "a diagram node outside the list", old := "Choice: 1", new := "Loop: 1",
     expect := .refuses "the unread node `Loop`" },
   { label := "a group with no node under it",
     old := "\t\tStar:\n\t\t\tN: c", new := "\t\tStar:",
     expect := .refuses "the node `Star` holds no node" },
   { label := "an element outside the list in a production", old := "f( <<number>> )",
     new := "f( <b>x</b> )", expect := .refuses "the unread element `b`" },
   { label := "a character reference outside the list in a production", old := "[ a | b ]#",
     new := "[ a | &copy; ]#", expect := .refuses "the unread character reference `&copy;`" },
   { label := "a keyword that names what it is a keyword of",
     old := "''auto''", new := "''width/auto''",
     expect := .refuses "the unread keyword `''width/auto''`" },
   { label := "a table cell that is neither marked nor empty", old := "<td> ", new := "<td>?",
     expect := .refuses "is neither marked nor empty" },
   { label := "a table row of another length",
     old := "<tr><th>y<td><td>", new := "<tr><th>y<td>",
     expect := .refuses "has 1 cells, and the table has 2 columns" },
   { label := "a listed anchor with no table under it",
     old := "", new := "", anchors := ["absent"],
     expect := .refuses "no table stands under the anchor `absent`" },
   { label := "a `div` that is not closed", old := "</div>\n<p>", new := "<p>",
     expect := .refuses "a `div` element is not closed" }]

/-- Whether `fragment` stands in `text`. -/
def holds (text fragment : String) : Bool := (text.splitOn fragment).length > 1

/-- The controls that do not answer as planted, each with what it answered. -/
def failedControls : List String :=
  controls.filterMap fun c =>
    let source := if c.old.isEmpty then plantedSource else plantedSource.replace c.old c.new
    let planted := c.old.isEmpty || source != plantedSource
    let control : Module := { name := "control", path := "control", digest := "" }
    let answer := extractWith c.anchors control source.toUTF8
    let fail (why : String) : Option String := some s!"control `{c.label}`: {why}"
    if !planted then fail "the text to replace is not in the planted source"
    else
      match c.expect, answer with
      | .says lines, .ok e =>
        if said e == lines then none else fail s!"the reading says {said e}"
      | .properties count, .ok e =>
        if e.properties.length == count then none else fail s!"{e.properties.length} property rows"
      | .refuses fragment, .error message =>
        if holds message fragment then none else fail s!"refused for another reason: {message}"
      | .refuses _, .ok _ => fail "the source was read, and a refusal was due"
      | _, .error message => fail s!"refused: {message}"

/-! ## Driver -/

/-- Read one sealed module, and refuse a digest that is not the pinned one. -/
def readPinned (root : System.FilePath) (m : Module) : IO ByteArray := do
  let path := root / m.path
  unless ← path.pathExists do
    throw <| IO.userError s!"css blocks: missing input {m.path}"
  let bytes ← IO.FS.readBinFile path
  let digest := Gates.Sha256.hexDigest bytes
  unless digest == m.digest do
    throw <| IO.userError
      (s!"css blocks: {m.path} has digest {digest}, expected the pinned {m.digest}; " ++
        "re-pin before regenerating")
  return bytes

/-- A refusal as an error of the gate. -/
def liftExcept {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw <| IO.userError s!"css blocks: {e}"

/-- Read every module of a list through `read`, and render every file. -/
def generate (read : Module → IO ByteArray) (modules : List Module) :
    IO (List Extract × List (String × String)) := do
  let mut extracts : List Extract := []
  for m in modules do
    extracts := extracts ++ [← liftExcept (extract m (← read m))]
  return (extracts, ← liftExcept (outputs extracts))

/-- One line for each module: its blocks, then its rows. -/
def summarize (es : List Extract) : String :=
  String.join (es.map fun e =>
    s!"css blocks: {e.module.name}: blocks {blockCount e "propdef"} propdef, " ++
    s!"{blockCount e "descdef"} descdef, {blockCount e "prod"} prod, " ++
    s!"{blockCount e "pre"} bare pre, {blockCount e "railroad"} railroad, " ++
    s!"{e.tables.length} table; rows {e.properties.length} " ++
    s!"property, {e.descriptors.length} descriptor, {e.productions.length} production, " ++
    s!"{e.diagrams.length} diagram; {e.passed} block tags passed over in comments and raw text\n")

/-- The drift of committed files against fresh text: nothing when every file is identical. The
first ten differing lines of a file are shown. -/
def driftOf (root : System.FilePath) (files : List (String × String)) : IO (List String) := do
  let mut failures : List String := []
  for (relative, fresh) in files do
    let path := root / relative
    unless ← path.pathExists do
      failures := failures ++ [s!"missing {relative}; run `lake exe whatwg_cssblocks --write`"]
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

/-- The files of the tables directory that no module accounts for. -/
def straysOf (root : System.FilePath) (files : List (String × String)) : IO (List String) := do
  let directory := root / tablesDirectory
  unless ← directory.pathExists do return []
  let mut found : List String := []
  for entry in ← directory.readDir do
    let relative := s!"{tablesDirectory}/{entry.fileName}"
    unless files.any (·.1 == relative) do
      found := found ++ [s!"unexpected {relative}: no sealed module accounts for it"]
  return found.mergeSort

/-- Write every file under `root`, and say so. -/
def writeFiles (root : System.FilePath) (files : List (String × String)) : IO Unit := do
  for (relative, text) in files do
    let path := root / relative
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path text
    IO.println s!"WROTE {relative}"

/-- Run the controls, and print each that does not answer as planted. -/
def runControls : IO Bool := do
  let failed := failedControls
  for failure in failed do IO.eprintln failure
  return failed.isEmpty

/-- Check the files under `root` against `files`, and run the controls. -/
def check (root : System.FilePath) (es : List Extract) (files : List (String × String)) :
    IO UInt32 := do
  IO.print (summarize es)
  let failures := (← driftOf root files) ++ (← straysOf root files)
  for failure in failures do IO.eprintln failure
  let sound ← runControls
  if failures.isEmpty && sound then
    IO.println <|
      s!"PASS css blocks: {es.length} sealed modules of {pinDirectory} have their pinned " ++
      "digests and are read with no construct refused, and each opening tag with a block class " ++
      s!"is a block read or a tag counted as passed over; {files.length} files, the tables and " ++
      s!"the index under {tablesDirectory}/ and {pairsPath}, are byte-identical to a fresh " ++
      s!"regeneration, and {tablesDirectory}/ holds no other file; {controls.length} controls " ++
      "answered as planted. The extractor is code that no theorem checks: a PASS is its verdict"
    return 0
  IO.eprintln "FAIL css blocks"
  return 1

/-- The three ways to call the gate. -/
def usage : String :=
  "usage: lake exe whatwg_cssblocks             check the tables of generated/css/ and the " ++
  "module of pairs against a regeneration, and run the controls\n" ++
  "       lake exe whatwg_cssblocks --write     regenerate them from the sealed CSS modules\n" ++
  "       lake exe whatwg_cssblocks --selftest  run the controls alone"

/-- Command-line entry, invoked by `whatwgbin/CssBlocks.lean`. -/
def cli (args : List String) : IO UInt32 := do
  try
    let root ← Gates.Common.projectRoot
    match args with
    | [] =>
      let (es, files) ← generate (readPinned root) sealedModules
      check root es files
    | ["--write"] =>
      let (es, files) ← generate (readPinned root) sealedModules
      writeFiles root files
      IO.print (summarize es)
      for stray in ← straysOf root files do IO.eprintln stray
      return 0
    | ["--selftest"] =>
      if ← runControls then
        IO.println s!"PASS css blocks: {controls.length} controls answered as planted"
        return 0
      IO.eprintln "FAIL css blocks: controls"
      return 1
    | _ =>
      IO.eprintln usage
      return 2
  catch err =>
    IO.eprintln s!"FAIL {err}"
    return 1

end Gates.CssBlocksEmit
