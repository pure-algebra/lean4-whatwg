import Gates.UrlCensus

/-!
URL authored census reader and deterministic source projections.
Declaration record and byte formats: `docs/URL-CENSUS-INPUT-INTERFACE.md`.
This validates authored joins; it supplies no URL execution or coverage judgment.
Regenerate both TSVs with `lake exe urlcensus --write`; check with `lake exe urlcensus`.
-/

namespace Gates.UrlCensusInput

structure Inputs where
  spans : String
  explanations : String
  dispositions : String
  overrides : String
  dependencies : String
  externals : String
  deriving Inhabited

private def space (c : Char) : Bool := [9, 10, 12, 13, 32].contains c.toNat

private def dataLines (text : String) : List String :=
  (Gates.Common.lines text).filter fun line ↦
    let start := String.ofList (line.toList.dropWhile space)
    !start.isEmpty && !start.startsWith "#"

/-- Add a terminator for the shared parser to consume, retaining every existing field byte. -/
private def forSharedParser (lines : List String) : String :=
  String.join (lines.map (· ++ "\r\n"))

private def identity (text : String) : Bool :=
  !text.isEmpty && text.toList.all fun c ↦
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
    ('0' ≤ c && c ≤ '9') || ['.', '_', '-'].contains c

private def natToken (text : String) : Except String Nat := do
  if text.isEmpty || !text.toList.all (fun c ↦ '0' ≤ c && c ≤ '9') ||
      (text != "0" && text.startsWith "0") then
    throw s!"noncanonical natural number {text}"
  let some n := text.toNat? | throw s!"invalid natural number {text}"
  return n

private def idToken (text : String) : Except String String := do
  if !identity text then throw s!"invalid identity token {text}"
  return text

private def rowKind (id : String) : Except String Gates.Census.Kind := do
  let _ ← idToken id
  let kindText := (id.splitOn ".").headD ""
  let some kind := Gates.Census.Kind.ofString? kindText | throw s!"invalid row kind in {id}"
  if id == kindText || id == kindText ++ "." then throw s!"empty row suffix in {id}"
  return kind

private def anchorEnd (bs : ByteArray) (id : String) (b e : Nat) : Except String Nat := do
  if b ≥ e || e > bs.size || (String.fromUTF8? (bs.extract b e)).isNone then
    throw s!"invalid source span for {id}"
  let lengths := (Gates.Census.anchorLadder.filter (· < e - b)) ++ [e - b]
  for n in lengths do
    let stop := Gates.Census.alignForward bs (b + n)
    if stop ≤ e && Gates.Census.occurrences bs (bs.extract b stop) 2 == #[b] then
      return stop
  throw s!"row {id} has no unique prefix within its source span"

private def parseSpans (bs : ByteArray) (text : String) :
    Except String (Array Gates.UrlCensus.SourceRow) := do
  let mut rows : Array Gates.UrlCensus.SourceRow := #[]
  for line in dataLines text do
    let [id, bText, eText, originText, parentText] := line.splitOn "\t"
      | throw "spans: expected five tab-separated fields"
    let kind ← rowKind id
    if rows.any (·.row.id == id) then throw s!"duplicate span ID {id}"
    let b ← natToken bText
    let e ← natToken eText
    let origins ← (originText.splitOn ",").mapM natToken
    let parent ← if parentText == "-" then pure none else some <$> idToken parentText
    let stop ← anchorEnd bs id b e
    rows := rows.push {
      row := { kind, id, anchorB := b, anchorE := stop, spanB := b, spanE := e },
      disposition := .owned, parent, origins := origins.toArray }
  return rows

private def parseExplanations (text : String) :
    Except String (Array Gates.UrlCensus.Explanation) := do
  let mut rows := #[]
  for line in dataLines text do
    let [bText, eText, reason] := line.splitOn "\t"
      | throw "explanations: expected three tab-separated fields"
    let b ← natToken bText
    let e ← natToken eText
    rows := rows.push { b, e, reason }
  return rows

private def parseDispositions (text : String) :
    Except String (Array Gates.Census.DispositionRule) := do
  let lines := dataLines text
  for line in lines do
    let [sectionId, _, _] := line.splitOn "\t"
      | throw "dispositions: expected three tab-separated fields"
    if sectionId.isEmpty || sectionId.toList.any space then
      throw s!"invalid disposition section {sectionId}"
  Gates.Census.parseDispositions (forSharedParser lines) "census/url/dispositions.tsv"

private def parseOverrides (text : String) :
    Except String (Array Gates.Census.OverrideRule) := do
  let lines := dataLines text
  for line in lines do
    let [id, _, reason] := line.splitOn "\t"
      | throw "overrides: expected three tab-separated fields"
    let _ ← idToken id
    if reason.toList.all space then throw s!"override for {id} has no justification"
  Gates.Census.parseOverrides (forSharedParser lines) "census/url/overrides.tsv"

private def parseDependencies (text : String) : Except String (Array (String × Array String)) := do
  let mut rows : Array (String × Array String) := #[]
  for line in dataLines text do
    let [idText, depsText] := line.splitOn "\t"
      | throw "dependencies: expected two tab-separated fields"
    let id ← idToken idText
    if rows.any (·.1 == id) then throw s!"duplicate dependency entry for {id}"
    let deps ← if depsText == "-" then pure [] else (depsText.splitOn ",").mapM idToken
    rows := rows.push (id, deps.toArray)
  return rows

private def parseExternals (text : String) : Except String (Array String) := do
  let mut ids := #[]
  for line in dataLines text do
    let id ← idToken line
    if !id.startsWith "ext." || id == "ext." then throw s!"invalid external ID {id}"
    ids := ids.push id
  return ids

private def sectionAt (entries : Array Gates.UrlInventory.Entry) (b : Nat) : String := Id.run do
  let mut sectionId := ""
  for entry in entries do
    if entry.b > b then break
    if entry.kind == .heading then sectionId := entry.section
  return sectionId

/-- Read and validate the authored inputs, then run the strict source assignment. -/
def build (bs : ByteArray) (inputs : Inputs) :
    Except String (Array Gates.UrlCensus.SourceRow × Array Gates.UrlCensus.Assignment) := do
  let entries ← Gates.UrlInventory.scan bs
  let initialRows ← parseSpans bs inputs.spans
  let explanations ← parseExplanations inputs.explanations
  let rules ← parseDispositions inputs.dispositions
  let overrides ← parseOverrides inputs.overrides
  let dependencies ← parseDependencies inputs.dependencies
  let externals ← parseExternals inputs.externals
  let mut usedRules := Array.replicate rules.size false
  let mut usedOverrides := Array.replicate overrides.size false
  let mut rows := #[]
  for r in initialRows do
    let some (_, deps) := dependencies.find? (·.1 == r.row.id)
      | throw s!"missing dependency entry for {r.row.id}"
    let sectionId := sectionAt entries r.row.spanB
    let some (disposition, source) :=
        Gates.Census.resolveDisposition rules overrides (sectionId, "", "") r.row
      | throw s!"unresolved disposition for {r.row.id} in section {sectionId}"
    match source with
    | .fromOverride i => usedOverrides := usedOverrides.set! i true
    | .fromSection i => usedRules := usedRules.set! i true
    rows := rows.push { r with disposition, dependencies := deps }
  for (id, _) in dependencies do
    if !rows.any (·.row.id == id) then throw s!"unused dependency entry for {id}"
  for i in [:rules.size] do
    if !usedRules[i]! then throw s!"unused disposition rule {i + 1} ({rules[i]!.sectionId})"
  for i in [:overrides.size] do
    if !usedOverrides[i]! then throw s!"unused override for {overrides[i]!.rowId}"
  let assignments ← Gates.UrlCensus.assign bs rows explanations externals
  return (rows.qsort (fun a b ↦ a.row.sortKey < b.row.sortKey), assignments)

private def escape (text : String) : String :=
  text.toList.foldl (fun out c ↦ out ++ match c with
    | '\\' => "\\\\" | '\t' => "\\t" | '\n' => "\\n" | '\r' => "\\r"
    | _ => String.singleton c) ""

private def tsv (fields : List String) : String :=
  "\t".intercalate (fields.map escape) ++ "\n"

private def candidateKind : Gates.UrlInventory.Kind → String
  | .definition => "definition" | .algorithm => "algorithm" | .idl => "idl"
  | .prose => "prose" | .table => "table" | .list => "list" | .heading => "heading"

private def inputPairs (inputs : Inputs) : List (String × String) :=
  [("spans", inputs.spans), ("explanations", inputs.explanations),
   ("dispositions", inputs.dispositions), ("overrides", inputs.overrides),
   ("dependencies", inputs.dependencies), ("externals", inputs.externals)]

private def inputHashes (inputs : Inputs) : String :=
  String.join ((inputPairs inputs).map fun (name, value) ↦
    s!"#input {name}-sha256={Gates.Sha256.hexDigest value.toUTF8}\n")

/-- Render both projections only after all input and assignment checks succeed. -/
def project (bs : ByteArray) (inputs : Inputs) : Except String (String × String) := do
  let (rows, assignments) ← build bs inputs
  let digest := Gates.Sha256.hexDigest bs
  let hashes := inputHashes inputs
  let mut census :=
    s!"#url-census format=1 generator=Gates.UrlCensusInput input-sha256={digest} " ++
    s!"rows={rows.size}\n" ++
    "#kind\tid\tbyte-start\tbyte-end\tspan-sha256\tanchor-end\tanchor-sha256\tparent\t" ++
    "origins\tdisposition\tdependencies\n" ++ hashes
  for r in rows do
    let s := r.row
    census := census ++ tsv [s.kind.name, s.id, toString s.spanB, toString s.spanE,
      Gates.Sha256.hexDigest (bs.extract s.spanB s.spanE), toString s.anchorE,
      Gates.Sha256.hexDigest (bs.extract s.anchorB s.anchorE), r.parent.getD "-",
      ",".intercalate (r.origins.toList.map toString), r.disposition.name,
      if r.dependencies.isEmpty then "-" else ",".intercalate r.dependencies.toList]
  let mut inventory :=
    s!"#url-source-assignments format=1 generator=Gates.UrlCensusInput input-sha256={digest} " ++
    s!"candidates={assignments.size}\n" ++
    "#ordinal\tkind\tbyte-start\tbyte-end\tspan-sha256\tlabel\tsection\towner\treason\n" ++ hashes
  for i in [:assignments.size] do
    let a := assignments[i]!
    let c := a.candidate
    inventory := inventory ++ tsv [toString (i + 1), candidateKind c.kind,
      toString c.b, toString c.e, Gates.Sha256.hexDigest (bs.extract c.b c.e),
      c.label, c.section, a.owner.getD "-", a.reason]
  return (census, inventory)

private def readText (path : System.FilePath) : IO String := do
  let bs ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bs | throw <| IO.userError s!"invalid UTF-8: {path}"
  return text

private def readInputs (root : System.FilePath) : IO Inputs := do
  let dir := root / "census/url"
  return {
    spans := ← readText (dir / "spans.tsv"),
    explanations := ← readText (dir / "explanations.tsv"),
    dispositions := ← readText (dir / "dispositions.tsv"),
    overrides := ← readText (dir / "overrides.tsv"),
    dependencies := ← readText (dir / "dependencies.tsv"),
    externals := ← readText (dir / "externals.tsv") }

private def checkOrWrite (root : System.FilePath) (write : Bool) : IO UInt32 := do
  let bs ← IO.FS.readBinFile (root / "vendor/whatwg-url-55d66993/url.bs")
  let digest := Gates.Sha256.hexDigest bs
  let pinned := "a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805"
  if digest != pinned then
    throw <| IO.userError s!"source digest {digest} differs from pin {pinned}"
  let inputs ← readInputs root
  let (census, assignments) ← match project bs inputs with
    | .ok result => pure result
    | .error err => throw <| IO.userError err
  let outputs := [("generated/url-census.tsv", census),
    ("generated/url-source-assignments.tsv", assignments)]
  if write then
    IO.FS.createDirAll (root / "generated")
    for (name, expected) in outputs do
      IO.FS.writeBinFile (root / name) expected.toUTF8
      IO.println s!"WROTE {name}"
    IO.println "PASS URL census: pinned source, authored joins and both source projections written"
    return 0
  let mut failed := false
  for (name, expected) in outputs do
    let path := root / name
    if !(← path.pathExists) then
      IO.eprintln s!"FAIL URL census: missing projection {name}"
      failed := true
      continue
    let actual ← IO.FS.readBinFile path
    if actual == expected.toUTF8 then continue
    failed := true
    IO.eprintln s!"FAIL URL census: projection drift in {name}"
    -- Compare byte lines, including invalid UTF-8 and CRLF differences without normalization.
    let actualLines := actual.data.toList.splitOn 10
    let expectedLines := expected.toUTF8.data.toList.splitOn 10
    for i in [:max actualLines.length expectedLines.length] do
      if actualLines[i]? != expectedLines[i]? then
        IO.eprintln s!"  line {i + 1} stored bytes: {actualLines[i]?}"
        IO.eprintln s!"  line {i + 1} expected bytes: {expectedLines[i]?}"
  if failed then return 1
  IO.println "PASS URL census: pinned source, authored joins; both projections are byte-identical"
  return 0

/-- Check or regenerate the source census; no semantic numerator is emitted. -/
def cli (args : List String) : IO UInt32 := do
  let write ← match args with
    | [] => pure false
    | ["--write"] => pure true
    | _ =>
      IO.eprintln "usage: lake exe urlcensus [--write]"
      return 2
  try
    checkOrWrite (← Gates.Common.projectRoot) write
  catch err =>
    IO.eprintln s!"FAIL URL census: {err}"
    return 1

end Gates.UrlCensusInput
