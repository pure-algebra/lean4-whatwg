import Lean
import Gates

/-!
# Web IDL census Q2 addendum battery

Breaker-owned and frozen before the Q2 builder change. Packet:
`test/contracts/webidl-census-q2.contract.md`, an addendum to
`test/contracts/webidl-census.contract.md`, which stays frozen and unedited.
The addendum is the authority on every number below and on the meaning of
every name this file ascribes.

This battery is a tooling contract. It asserts no Web IDL semantics, no
observation mask and no coverage state above `absent`: the two coverage blocks
it freezes say that nothing is proved, and quoting either as coverage is a
defect.

Two red causes are expected before the builder lands the slice, and no other
error class:

1. `Gates.Census.cli` takes one `Array Gates.Census.CoverageRow` today, and
   section 6.2 of the addendum freezes the map
   `List (String × Array Gates.Census.CoverageRow)`; and
2. `generated/webidl-census.tsv` carries the 121 rows of Q1, and the addendum
   freezes 124, so the projection gate in section 4 stops on its first clause.

The gate is deliberately fail-fast, and its first clause is the row total
rather than the header line, because the row total is the fact every later
assertion is conditional on: a tree at Q1 gets one clear sentence instead of a
cascade.

Every span, digest and anchor length in section 2 was recomputed in the packet
from the sealed bytes of `vendor/whatwg-webidl-a652053f/index.bs`,
independently of `Gates.Census`, after the same re-implementation reproduced
three already-frozen Q1 rows exactly. The gate below recomputes each digest
with `Gates.Sha256.hexDigest` and each anchor length with the real
`Gates.Census.chooseAnchorLength` over the pinned bytes.
-/

set_option autoImplicit false

namespace WhatwgTest.Audit.WebIdl.CensusQ2Contract

open Lean Elab Command

/-! ## 1. The numerator and report API (Q2 acceptance 4)

`docs/SPEC-COVERAGE.md` prints coverage from the numerator's Lean emit, never
from a file a person can edit, and `Gates.Census.verifyEmit` re-derives ids,
order and dispositions from a fresh census regeneration before `report`
prints. Q2 gives Web IDL and ECMA-262 numerators of their own, so the one
entry point that carries an emit has to carry three.

The minimal signature change, ascribed here and frozen by section 6.2 of the
addendum, is a map from standard key to emit: the number of standards is
already four, an association list adds no case analysis at any call site, and
the alternative — one `Option` argument per standard — would put a
per-standard parameter into a signature whose only caller is `bin/Census.lean`.
Everything downstream keeps its current signature, which is why the four
ascriptions after it are green today and must stay green. -/

#check (@Gates.Census.CoverageRow : Type)
#check (@Gates.Census.CoverageRow.mk :
  String → Gates.Census.Disposition → Gates.Census.CoverageState → List String →
    Gates.Census.CoverageRow)
#check (Gates.Census.CoverageState.absent : Gates.Census.CoverageState)
#check (@Gates.Census.verifyEmit :
  Gates.Census.Built → Array Gates.Census.CoverageRow → Array String)
#check (@Gates.Census.check :
  System.FilePath → Gates.Census.Standard → Option (Array Gates.Census.CoverageRow) →
    IO UInt32)
#check (@Gates.Census.report :
  System.FilePath → Gates.Census.Standard → Array Gates.Census.CoverageRow → IO UInt32)

-- The one signature this slice changes.
#check (@Gates.Census.cli :
  List (String × Array Gates.Census.CoverageRow) → List String → IO UInt32)

/-! ## 2. The three rows the addendum adds

Debt D3 adds `DOMException`'s serialization and deserialization steps, which
are normative steps written as plain `<ol>` lists in running prose and which
therefore reach no scanner; debt D5 adds the reverse direction of the promise
conversion pair, a bare `<p id="promise-to-js">` paragraph whose forward
direction is the row `op.js-to-promise`. All three enter through
`census/webidl/rules.tsv` with ruling R-P4's optional end locator, so their
kind is `rule`.

`anchorLen` is the byte length `Gates.Census.chooseAnchorLength` selects; the
anchor itself is the first that many bytes of the span. The two step rows take
48 rather than 24 because both 24-byte and 32-byte prefixes recur in the
`QuotaExceededError` section, which states the same two sentences with the
Bikeshed variable spelling `|value|`. -/

private structure Frozen where
  kind : String
  id : String
  spanB : Nat
  spanE : Nat
  anchorLen : Nat
  digest : String
  deriving Inhabited

private def newRows : Array Frozen := #[
  ⟨"rule", "rule.domexception-deserialization-steps", 676693, 677111, 48,
    "56b4661e16e17c24d633c37423077ef96810a7d737f5e97ed657aebb08e35555"⟩,
  ⟨"rule", "rule.domexception-serialization-steps", 676192, 676691, 48,
    "1c9753a8ed03b7e0a7e5b238408cbc3347746d0a341277a910386969dadeb218"⟩,
  ⟨"rule", "rule.promise-to-js", 347211, 347495, 24,
    "ef392964ee06eff2e3fd5682ecbb9704d004d704ec7de1032f8d40d9d535a111"⟩
]

/-- The three `census/webidl/rules.tsv` entries: name, start locator, end
locator. Each start locator must occur exactly once in the whole pinned file —
the shorter `Their [=serialization steps=], given` occurs twice, at 216531 and
676192 — and each end locator must occur at or after its start locator, since
`Gates.Census.scanRules` refuses rather than widening to the blank-line
rule. -/
private def newRuleInputs : Array (String × String × String) := #[
  ("domexception-serialization-steps",
   "Their [=serialization steps=], given <var>value</var>",
   "Their [=deserialization steps=], given <var>value</var>"),
  ("domexception-deserialization-steps",
   "Their [=deserialization steps=], given <var>value</var>",
   "<h3 id=\"Function\" callback"),
  ("promise-to-js",
   "<p id=\"promise-to-js\">",
   "<h5 id=\"js-promise-manipulation\"")
]

/-- The three `census/webidl/dependencies.tsv` lines the new rows need, in the
file's existing sorted form. Derived from the `[=…=]`, `{{…}}` and `\[[…]]`
references inside each row's own byte span and from nothing else; every
identity is already declared in `census/webidl/externals.tsv` or is a row of
this census, so no external identity is added and none is orphaned. -/
private def newDependencyLines : Array (String × String) := #[
  ("rule.domexception-deserialization-steps",
   "ext.html.deserialization-steps,ext.html.serialized-record,op.dom-exception-message,op.dom-exception-name"),
  ("rule.domexception-serialization-steps",
   "ext.html.serialization-steps,ext.html.serialized-record,op.dom-exception-message,op.dom-exception-name"),
  ("rule.promise-to-js",
   "ext.ecma262.slot-promise,ext.webidl.js-type-mapping,op.dfn-promise-type")
]

/-! ## 3. The amended totals

Section 4 of the addendum. `owned` gains the two `idl-DOMException` `rule`
rows (D3, dispositioned by a new `idl-DOMException rule owned` line);
`hostOnly` gains `rule.promise-to-js` from the unchanged `js-promise *
hostOnly` line (D5) and `op.an-exception-was-thrown` from the amended
`js-handling-exceptions * hostOnly` line (D4); `evidenceOnly` loses that same
row. 61 + 49 + 8 + 6 = 124 and 124 − 8 = 116. -/

private def sourceRelativePath : String := "vendor/whatwg-webidl-a652053f/index.bs"

private def sourceDigest : String :=
  "3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83"

private def censusRelativePath : String := "generated/webidl-census.tsv"

private def rowsRelativePath : String := "WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean"

private def infraCensusRelativePath : String := "generated/infra-census.tsv"

private def rulesRelativePath : String := "census/webidl/rules.tsv"

private def dependenciesRelativePath : String := "census/webidl/dependencies.tsv"

private def externalsRelativePath : String := "census/webidl/externals.tsv"

private def numeratorRelativePath : String := "WhatwgTest/Audit/WebIdl/SpecCoverage.lean"

private def entryPointRelativePath : String := "bin/Census.lean"

private def coverageDocRelativePath : String := "docs/SPEC-COVERAGE.md"

private def regenerateCommand : String := "lake exe census --standard webidl --write"

private def expectedRowTotal : Nat := 124

private def expectedDenominator : Nat := 116

private def expectedHeader : String :=
  "#census format=1 generator=Gates.Census input=vendor/whatwg-webidl-a652053f/index.bs " ++
  "input-sha256=3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83 " ++
  "rows=124 regenerate=lake exe census --standard webidl --write"

private def expectedKindCounts : List (String × Nat) :=
  [("idl", 37), ("op", 39), ("requirement", 0), ("rule", 9), ("slot", 0), ("type", 39),
   ("builtin", 0), ("hook", 0), ("property", 0), ("record", 0), ("field", 0),
   ("term", 0), ("clause", 0)]

private def expectedDispositionCounts : List (String × Nat) :=
  [("owned", 61), ("hostOnly", 49), ("evidenceOnly", 8), ("requirement", 6),
   ("foreignBoundary", 0), ("refused", 0), ("targetOnly", 0)]

/-- Debt D4: an exported normative `<dfn>` under a sentence that requires
propagation is a host obligation, not an example, so this row is inside the
denominator where a host-profile refusal can be recorded against it. -/
private def expectedRowsModuleLines : List String :=
  ["  ⟨\"op.an-exception-was-thrown\", .hostOnly, .absent, []⟩,",
   "  ⟨\"rule.domexception-deserialization-steps\", .owned, .absent, []⟩,",
   "  ⟨\"rule.domexception-serialization-steps\", .owned, .absent, []⟩,",
   "  ⟨\"rule.promise-to-js\", .hostOnly, .absent, []⟩,"]

/-- The frozen source text of the two Q2 numerator obligations. The numerator
module carries the same shape `WhatwgTest/Audit/SpecCoverage.lean` has for
Streams, so a census change that invalidates the freeze is repaired in the
same edit. -/
private def expectedNumeratorFragments : List String :=
  ["import WhatwgTest.Audit.WebIdl.SpecCoverageRows",
   "namespace WhatwgTest.Audit.WebIdl.SpecCoverage",
   "def emit : Array CoverageRow :=",
   "def expectedRowTotal : Nat := 124",
   "def expectedDenominator : Nat := 116"]

private def expectedEntryPointFragments : List String :=
  ["import WhatwgTest.Audit.WebIdl.SpecCoverage",
   "import WhatwgTest.Audit.Ecma262.SpecCoverage",
   "(\"streams\", WhatwgTest.Audit.SpecCoverage.emit)",
   "(\"webidl\", WhatwgTest.Audit.WebIdl.SpecCoverage.emit)",
   "(\"ecma262\", WhatwgTest.Audit.Ecma262.SpecCoverage.emit)"]

/-- The all-`absent` coverage block, in the three-line format
`docs/SPEC-COVERAGE.md` owns, which Q2 pastes over the placeholder block that
says every field is a placeholder. `owned-with-green 0/116` and `green 0` are
the whole content of the claim. -/
private def expectedCoverageBlock : String :=
  "WHATWG Web IDL (a652053f) coverage: denominator 116; owned-with-green 0/116;\n" ++
  "green 0, partial 0, absent 116; census 124 rows, 8 excluded\n" ++
  "partial:"

/-! ## 4. The projection, input and report gate -/

private def occurrencesOf (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

/-- The row ids of a generated census projection, in file order. -/
private def censusRowIdsOf (text : String) : List String :=
  ((Gates.Common.lines text).drop 1).filterMap fun line =>
    match Gates.Census.splitRow line with
    | .ok fields => if fields.size == 7 then some (fields.getD 1 "") else none
    | .error _ => none

private def dependencyTargets (field : String) : List String :=
  if field == "-" then [] else field.splitOn ","

open Elab Command in
elab "#webidl_census_q2_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "webidl census Q2 contract: source file has no parent directory"
  let projectRoot ← liftIO <| Gates.Common.findProjectRoot sourceDirectory
  let some standard := Gates.Census.Standard.ofKey? "webidl"
    | throwError "webidl census Q2 contract: no standard is registered under the key webidl"
  if standard.censusRelativePath != censusRelativePath then
    throwError "webidl census Q2 contract: the standard writes {standard.censusRelativePath}; the addendum freezes {censusRelativePath}"
  let censusPath := projectRoot / censusRelativePath
  unless ← liftIO censusPath.pathExists do
    throwError "webidl census Q2 contract: missing {censusRelativePath}; run `{regenerateCommand}`"
  let sourcePath := projectRoot / sourceRelativePath
  unless ← liftIO sourcePath.pathExists do
    throwError "webidl census Q2 contract: missing the pinned source {sourceRelativePath}"
  let bytes ← liftIO <| IO.FS.readBinFile sourcePath
  let censusText ← liftIO <| IO.FS.readFile censusPath
  let allLines := Gates.Common.lines censusText
  let header := allLines.headD ""
  let dataLines := allLines.drop 1
  -- The row total first: every clause below is conditional on it.
  if dataLines.length != expectedRowTotal then
    throwError "webidl census Q2 contract: {censusRelativePath} carries {dataLines.length} rows; the addendum freezes {expectedRowTotal}"
  if header != expectedHeader then
    throwError "webidl census Q2 contract: the header line of {censusRelativePath} is not the frozen one"
  let mut parsed : Array (Array String) := #[]
  let mut lineNumber : Nat := 1
  for line in dataLines do
    lineNumber := lineNumber + 1
    match Gates.Census.splitRow line with
    | .error message =>
      throwError "webidl census Q2 contract: line {lineNumber}: {message}"
    | .ok fields =>
      if fields.size != 7 then
        throwError "webidl census Q2 contract: line {lineNumber}: expected seven fields, found {fields.size}"
      parsed := parsed.push fields
  for i in [1:parsed.size] do
    let previous := (parsed.getD (i - 1) #[]).getD 0 "" ++ "|" ++ (parsed.getD (i - 1) #[]).getD 1 ""
    let current := (parsed.getD i #[]).getD 0 "" ++ "|" ++ (parsed.getD i #[]).getD 1 ""
    unless previous < current do
      throwError "webidl census Q2 contract: rows {i} and {i + 1} are not strictly increasing in kind then id ({previous}, {current})"
  for (kindName, expected) in expectedKindCounts do
    let observed := parsed.foldl (fun acc fields => if fields.getD 0 "" == kindName then acc + 1 else acc) 0
    unless observed == expected do
      throwError "webidl census Q2 contract: {censusRelativePath} holds {observed} {kindName} row(s); the addendum freezes {expected}"
  -- The three new rows, byte for byte, with the digest and the anchor ladder
  -- recomputed from the pinned bytes rather than read back from the table.
  for row in newRows do
    let some fields := parsed.find? (fun f => f.getD 0 "" == row.kind && f.getD 1 "" == row.id)
      | throwError "webidl census Q2 contract: {censusRelativePath} has no {row.kind} row {row.id}"
    let anchorField := fields.getD 2 ""
    let startField := fields.getD 3 ""
    let endField := fields.getD 4 ""
    let digestField := fields.getD 5 ""
    if startField != toString row.spanB then
      throwError "webidl census Q2 contract: {row.id} starts at {startField}; the addendum freezes {row.spanB}"
    if endField != toString row.spanE then
      throwError "webidl census Q2 contract: {row.id} ends at {endField}; the addendum freezes {row.spanE}"
    if digestField != row.digest then
      throwError "webidl census Q2 contract: {row.id} records span digest {digestField}; the addendum freezes {row.digest}"
    let recomputed := Gates.Sha256.hexDigest (bytes.extract row.spanB row.spanE)
    if recomputed != row.digest then
      throwError "webidl census Q2 contract: the pinned bytes [{row.spanB}, {row.spanE}) hash to {recomputed}; the addendum freezes {row.digest} for {row.id}"
    let some anchor := Gates.Census.sliceString? bytes row.spanB (row.spanB + row.anchorLen)
      | throwError "webidl census Q2 contract: the {row.anchorLen}-byte anchor of {row.id} is not valid UTF-8"
    if anchorField != anchor then
      throwError "webidl census Q2 contract: the anchor of {row.id} is not the first {row.anchorLen} bytes of its span"
    match Gates.Census.chooseAnchorLength bytes row.spanB with
    | .error rival =>
      throwError "webidl census Q2 contract: the real anchor ladder finds no unique anchor for {row.id}; its span start is repeated at byte {rival}"
    | .ok chosen =>
      unless chosen == row.anchorLen do
        throwError "webidl census Q2 contract: Gates.Census.chooseAnchorLength selects {chosen} bytes for {row.id}; the addendum freezes {row.anchorLen}"
  -- The authored rule entries, and the locator uniqueness scanRules demands.
  let rulesPath := projectRoot / rulesRelativePath
  unless ← liftIO rulesPath.pathExists do
    throwError "webidl census Q2 contract: missing {rulesRelativePath}"
  let ruleEntries := Gates.Common.listFileEntries (← liftIO <| IO.FS.readFile rulesPath)
  for (name, startLocator, endLocator) in newRuleInputs do
    let expectedLine := name ++ "\t" ++ startLocator ++ "\t" ++ endLocator
    unless ruleEntries.contains expectedLine do
      throwError "webidl census Q2 contract: {rulesRelativePath} has no entry for {name} with the frozen start and end locators"
    let hits := Gates.Census.occurrences bytes startLocator.toUTF8 2
    unless hits.size == 1 do
      throwError "webidl census Q2 contract: the start locator of {name} occurs {hits.size} time(s) in {sourceRelativePath}; Gates.Census.scanRules requires exactly one"
    let some start := hits[0]?
      | throwError "webidl census Q2 contract: the start locator of {name} does not occur in {sourceRelativePath}"
    let some _ := Gates.Census.findFrom bytes endLocator.toUTF8 start
      | throwError "webidl census Q2 contract: the end locator of {name} does not occur at or after its start locator; Gates.Census.scanRules refuses rather than widening to the blank-line rule"
  -- The generated numerator scaffold, with the amended totals and the three
  -- dispositions the addendum decides.
  let rowsPath := projectRoot / rowsRelativePath
  unless ← liftIO rowsPath.pathExists do
    throwError "webidl census Q2 contract: missing {rowsRelativePath}; run `{regenerateCommand}`"
  let rowsText ← liftIO <| IO.FS.readFile rowsPath
  let rowsLines := Gates.Common.lines rowsText
  unless rowsLines.contains s!"def rowTotal : Nat := {expectedRowTotal}" do
    throwError "webidl census Q2 contract: {rowsRelativePath} does not record rowTotal {expectedRowTotal}"
  unless rowsLines.contains s!"def denominator : Nat := {expectedDenominator}" do
    throwError "webidl census Q2 contract: {rowsRelativePath} does not record denominator {expectedDenominator}"
  for (dispositionName, expected) in expectedDispositionCounts do
    let observed := occurrencesOf rowsText (", ." ++ dispositionName ++ ",")
    unless observed == expected do
      throwError "webidl census Q2 contract: {rowsRelativePath} carries {observed} {dispositionName} row(s); the addendum freezes {expected}"
  for expectedLine in expectedRowsModuleLines do
    unless rowsLines.contains expectedLine do
      throwError "webidl census Q2 contract: {rowsRelativePath} does not carry the frozen entry {expectedLine}"
  -- Q2 acceptance 2, re-checked here independently of
  -- Gates.Census.checkDependencies: one dependency list per row in both
  -- directions, every declared external used, every target resolvable.
  let dependenciesPath := projectRoot / dependenciesRelativePath
  let externalsPath := projectRoot / externalsRelativePath
  let infraCensusPath := projectRoot / infraCensusRelativePath
  unless ← liftIO dependenciesPath.pathExists do
    throwError "webidl census Q2 contract: missing {dependenciesRelativePath}"
  unless ← liftIO externalsPath.pathExists do
    throwError "webidl census Q2 contract: missing {externalsRelativePath}"
  unless ← liftIO infraCensusPath.pathExists do
    throwError "webidl census Q2 contract: missing {infraCensusRelativePath}, which the cross-census join reads"
  let dependencyEntries := Gates.Common.listFileEntries (← liftIO <| IO.FS.readFile dependenciesPath)
  let externals := Gates.Common.listFileEntries (← liftIO <| IO.FS.readFile externalsPath)
  let infraRowIds := censusRowIdsOf (← liftIO <| IO.FS.readFile infraCensusPath)
  let censusRowIds := censusRowIdsOf censusText
  let mut owners : List String := []
  let mut usedExternals : List String := []
  for entry in dependencyEntries do
    match entry.splitOn "\t" with
    | [rowId, targetField] =>
      unless censusRowIds.contains rowId do
        throwError "webidl census Q2 contract: {dependenciesRelativePath} names {rowId}, which is not a row of {censusRelativePath}"
      if owners.contains rowId then
        throwError "webidl census Q2 contract: {dependenciesRelativePath} carries two lines for {rowId}"
      owners := rowId :: owners
      for target in dependencyTargets targetField do
        if target == rowId then
          throwError "webidl census Q2 contract: {dependenciesRelativePath} makes {rowId} depend on itself"
        if target.startsWith "ext." then
          unless externals.contains target do
            throwError "webidl census Q2 contract: {dependenciesRelativePath} names the undeclared external {target}"
          unless usedExternals.contains target do
            usedExternals := target :: usedExternals
        else
          unless censusRowIds.contains target || infraRowIds.contains target do
            throwError "webidl census Q2 contract: {dependenciesRelativePath} names {target}, which is neither a row of this census, a row of {infraCensusRelativePath}, nor a declared external"
    | _ =>
      throwError "webidl census Q2 contract: {dependenciesRelativePath} line `{entry}` is not two tab-separated fields"
  for rowId in censusRowIds do
    unless owners.contains rowId do
      throwError "webidl census Q2 contract: {dependenciesRelativePath} carries no line for the census row {rowId}"
  for identity in externals do
    unless usedExternals.contains identity do
      throwError "webidl census Q2 contract: {externalsRelativePath} declares {identity}, which no dependency line uses"
  for (rowId, targetField) in newDependencyLines do
    unless dependencyEntries.contains (rowId ++ "\t" ++ targetField) do
      throwError "webidl census Q2 contract: {dependenciesRelativePath} does not carry the frozen line for {rowId}"
  -- Q2 acceptance 4: the numerator, the entry point and the emitted block.
  let numeratorPath := projectRoot / numeratorRelativePath
  unless ← liftIO numeratorPath.pathExists do
    throwError "webidl census Q2 contract: missing {numeratorRelativePath}, the Web IDL coverage numerator the report is printed from"
  let numeratorText ← liftIO <| IO.FS.readFile numeratorPath
  for fragment in expectedNumeratorFragments do
    unless occurrencesOf numeratorText fragment > 0 do
      throwError "webidl census Q2 contract: {numeratorRelativePath} does not carry `{fragment}`"
  let entryPointPath := projectRoot / entryPointRelativePath
  unless ← liftIO entryPointPath.pathExists do
    throwError "webidl census Q2 contract: missing {entryPointRelativePath}"
  let entryPointText ← liftIO <| IO.FS.readFile entryPointPath
  for fragment in expectedEntryPointFragments do
    unless occurrencesOf entryPointText fragment > 0 do
      throwError "webidl census Q2 contract: {entryPointRelativePath} does not carry `{fragment}`; section 6.2 of the addendum freezes the standard-key-to-emit map"
  let coverageDocPath := projectRoot / coverageDocRelativePath
  unless ← liftIO coverageDocPath.pathExists do
    throwError "webidl census Q2 contract: missing {coverageDocRelativePath}"
  let coverageDocText ← liftIO <| IO.FS.readFile coverageDocPath
  unless occurrencesOf coverageDocText expectedCoverageBlock > 0 do
    throwError "webidl census Q2 contract: {coverageDocRelativePath} does not carry the all-absent Web IDL coverage block the Lean emit prints; the Q1 placeholder block is still there"
  logInfo
    m!"webidl census Q2 contract: {expectedRowTotal} rows, denominator {expectedDenominator}, {newRows.size} new rule rows verified against {sourceRelativePath} (SHA-256 {sourceDigest}) with the real anchor ladder, {censusRowIds.length} dependency lines and {externals.length} externals used in both directions, and the all-absent coverage block emitted"

#webidl_census_q2_gate

end WhatwgTest.Audit.WebIdl.CensusQ2Contract
