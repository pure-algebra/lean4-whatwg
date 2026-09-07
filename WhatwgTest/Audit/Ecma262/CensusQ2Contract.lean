import Lean
import Gates

/-!
# ECMA-262 census Q2 addendum battery

Breaker-owned and frozen before the Q2 builder change. Packet:
`test/contracts/ecma262-census-q2.contract.md`, an addendum to
`test/contracts/ecma262-census.contract.md`, which stays frozen and unedited.
The addendum is the authority on every number below.

This battery is a tooling contract. It asserts no ECMAScript semantics, no
observation mask and no coverage state above `absent`; in particular it does
not decide DB-03, and moving `clause.promise-objects` into the denominator
makes that row *owed* a witness, which is not the same as holding one. The
coverage block it freezes says that nothing is proved.

Two red causes are expected before the builder lands the slice, and no other
error class:

1. `Gates.Census.cli` takes one `Array Gates.Census.CoverageRow` today, and
   section 6.2 of `test/contracts/webidl-census-q2.contract.md` freezes the
   map `List (String × Array Gates.Census.CoverageRow)`; and
2. `WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean` records the denominator 74
   of Q1, and the addendum freezes 75, so the projection gate in section 3
   stops on its first amended clause.

This addendum recomputes no span and adds no row: it moves one row between two
dispositions. The one span it cites, `clause.promise-objects` at
2686444–2746707, is re-read from the pinned bytes and re-digested by the gate
below.
-/

set_option autoImplicit false

namespace WhatwgTest.Audit.Ecma262.CensusQ2Contract

open Lean Elab Command

/-! ## 1. The numerator and report API (Q2 acceptance 4)

The signature change is frozen once, in section 6.2 of
`test/contracts/webidl-census-q2.contract.md`: `Gates.Census.cli` takes a map
from standard key to emit, so that the one entry point carrying an emit can
carry three. It is ascribed again here because
`lake build WhatwgTest.Audit.Ecma262.CensusQ2Contract` is a narrow command
that has to stand on its own. -/

#check (@Gates.Census.CoverageRow : Type)
#check (Gates.Census.CoverageState.absent : Gates.Census.CoverageState)
#check (@Gates.Census.verifyEmit :
  Gates.Census.Built → Array Gates.Census.CoverageRow → Array String)
#check (@Gates.Census.report :
  System.FilePath → Gates.Census.Standard → Array Gates.Census.CoverageRow → IO UInt32)

-- The one signature this slice changes.
#check (@Gates.Census.cli :
  List (String × Array Gates.Census.CoverageRow) → List String → IO UInt32)

/-! ## 2. The amended totals

Section 2 of the addendum. Debt D4 moves `clause.promise-objects` from
`evidenceOnly` to `owned`: its own prose is the fulfilled/rejected/pending and
settled/resolved/unresolved vocabulary that `Whatwg.Ecma262.Promise.State`
realizes under ruling R-P13, so it is a row the model answers to rather than
evidence for something else. Its two siblings are bare headings whose own
prose is a section title, and they stay `evidenceOnly`.

The row total, the per-kind counts and every span, anchor and digest of the
base packet are unchanged: this addendum adds no row.
45 + 13 + 10 + 7 + 2 = 77 and 77 − 2 = 75. -/

private def sourceRelativePath : String := "vendor/ecma262-0248456c/spec.html"

private def sourceDigest : String :=
  "ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0"

private def censusRelativePath : String := "generated/ecma262-census.tsv"

private def rowsRelativePath : String := "WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean"

private def overridesRelativePath : String := "census/ecma262/overrides.tsv"

private def dependenciesRelativePath : String := "census/ecma262/dependencies.tsv"

private def externalsRelativePath : String := "census/ecma262/externals.tsv"

private def scannerBatteryRelativePath : String :=
  "WhatwgTest/Audit/Ecma262/EcmarkupScanner.lean"

private def numeratorRelativePath : String := "WhatwgTest/Audit/Ecma262/SpecCoverage.lean"

private def entryPointRelativePath : String := "bin/Census.lean"

private def coverageDocRelativePath : String := "docs/SPEC-COVERAGE.md"

private def regenerateCommand : String := "lake exe census --standard ecma262 --write"

private def expectedRowTotal : Nat := 77

private def expectedDenominator : Nat := 75

/-- Unchanged: the row count does not move, so the frozen header does not
either. -/
private def expectedHeader : String :=
  "#census format=1 generator=Gates.Census input=vendor/ecma262-0248456c/spec.html " ++
  "input-sha256=ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0 " ++
  "rows=77 regenerate=lake exe census --standard ecma262 --write"

private def expectedKindCounts : List (String × Nat) :=
  [("builtin", 13), ("clause", 8), ("field", 8), ("hook", 6), ("op", 16),
   ("property", 3), ("record", 3), ("requirement", 9), ("slot", 5), ("term", 6),
   ("idl", 0), ("rule", 0), ("type", 0)]

private def expectedDispositionCounts : List (String × Nat) :=
  [("owned", 45), ("foreignBoundary", 13), ("hostOnly", 10), ("requirement", 7),
   ("evidenceOnly", 2), ("refused", 0), ("targetOnly", 0)]

/-- The one row that moves, and the two siblings that must not move with it.
A blanket section label would have carried all three; separating them is the
whole content of the amendment. -/
private def expectedRowsModuleLines : List String :=
  ["  ⟨\"clause.promise-objects\", .owned, .absent, []⟩,",
   "  ⟨\"clause.promise-abstract-operations\", .evidenceOnly, .absent, []⟩,",
   "  ⟨\"clause.promise-jobs\", .evidenceOnly, .absent, []⟩,"]

/-- The moved row's span and digest, re-read from the pinned bytes here so the
amendment names a byte range rather than an id. -/
private def movedRowId : String := "clause.promise-objects"

private def movedRowSpanB : Nat := 2686444

private def movedRowSpanE : Nat := 2746707

private def movedRowDigest : String :=
  "21deb38546b2e5e928888349f91a40a16074a8cfa7f91469a0aec56c5bc7e9e0"

/-- Amendment 1.1 is authored in `dispositions.tsv`, never in
`overrides.tsv`: `Gates.Census.finishBuild` credits an overridden row to the
override alone, so an override would leave the clause's own line matching no
row and generation would fail. These three row ids are exactly the Q1
overrides and must stay exactly three. -/
private def expectedOverrideRowIds : List String :=
  ["field.jobcallback-records.Callback",
   "requirement.hostenqueuepromisejob.3",
   "term.job"]

/-- Q2 acceptance 5 is already discharged by the Q1 scanner battery, which
runs the real `Gates.Census.chooseAnchorLength` over the two rows the plan
names and over the lane's shortest anchor. This battery asserts that those
probes are still there with those lengths rather than paying for the ladder a
second time: one call scans all 2,978,793 pinned bytes. -/
private def expectedScannerProbeFragments : List String :=
  ["private def anchorLengthProbes : List (String × Nat × Nat) :=",
   "(\"field.jobcallback-records.HostDefined\", 629941, 256)",
   "(\"field.promisecapability-records.Promise\", 2688749, 64)",
   "(\"term.%Promise%\", 2707710, 24)"]

private def expectedNumeratorFragments : List String :=
  ["import WhatwgTest.Audit.Ecma262.SpecCoverageRows",
   "namespace WhatwgTest.Audit.Ecma262.SpecCoverage",
   "def emit : Array CoverageRow :=",
   "def expectedRowTotal : Nat := 77",
   "def expectedDenominator : Nat := 75"]

private def expectedEntryPointFragments : List String :=
  ["import WhatwgTest.Audit.Ecma262.SpecCoverage",
   "(\"ecma262\", WhatwgTest.Audit.Ecma262.SpecCoverage.emit)"]

/-- The all-`absent` coverage block, in the three-line format
`docs/SPEC-COVERAGE.md` owns. `owned-with-green 0/75` and `green 0` are the
whole content of the claim. -/
private def expectedCoverageBlock : String :=
  "ECMAScript ES2026 (0248456c) coverage: denominator 75; owned-with-green 0/75;\n" ++
  "green 0, partial 0, absent 75; census 77 rows, 2 excluded\n" ++
  "partial:"

/-! ## 3. The projection, input and report gate -/

private def occurrencesOf (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

private def censusRowIdsOf (text : String) : List String :=
  ((Gates.Common.lines text).drop 1).filterMap fun line =>
    match Gates.Census.splitRow line with
    | .ok fields => if fields.size == 7 then some (fields.getD 1 "") else none
    | .error _ => none

private def dependencyTargets (field : String) : List String :=
  if field == "-" then [] else field.splitOn ","

open Elab Command in
elab "#ecma262_census_q2_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "ecma262 census Q2 contract: source file has no parent directory"
  let projectRoot ← liftIO <| Gates.Common.findProjectRoot sourceDirectory
  let some standard := Gates.Census.Standard.ofKey? "ecma262"
    | throwError "ecma262 census Q2 contract: no standard is registered under the key ecma262"
  if standard.censusRelativePath != censusRelativePath then
    throwError "ecma262 census Q2 contract: the standard writes {standard.censusRelativePath}; the addendum freezes {censusRelativePath}"
  let censusPath := projectRoot / censusRelativePath
  unless ← liftIO censusPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {censusRelativePath}; run `{regenerateCommand}`"
  let sourcePath := projectRoot / sourceRelativePath
  unless ← liftIO sourcePath.pathExists do
    throwError "ecma262 census Q2 contract: missing the pinned source {sourceRelativePath}"
  let bytes ← liftIO <| IO.FS.readBinFile sourcePath
  let censusText ← liftIO <| IO.FS.readFile censusPath
  let allLines := Gates.Common.lines censusText
  let header := allLines.headD ""
  let dataLines := allLines.drop 1
  if dataLines.length != expectedRowTotal then
    throwError "ecma262 census Q2 contract: {censusRelativePath} carries {dataLines.length} rows; the addendum freezes {expectedRowTotal}"
  if header != expectedHeader then
    throwError "ecma262 census Q2 contract: the header line of {censusRelativePath} is not the frozen one"
  let mut parsed : Array (Array String) := #[]
  let mut lineNumber : Nat := 1
  for line in dataLines do
    lineNumber := lineNumber + 1
    match Gates.Census.splitRow line with
    | .error message =>
      throwError "ecma262 census Q2 contract: line {lineNumber}: {message}"
    | .ok fields =>
      if fields.size != 7 then
        throwError "ecma262 census Q2 contract: line {lineNumber}: expected seven fields, found {fields.size}"
      parsed := parsed.push fields
  for i in [1:parsed.size] do
    let previous := (parsed.getD (i - 1) #[]).getD 0 "" ++ "|" ++ (parsed.getD (i - 1) #[]).getD 1 ""
    let current := (parsed.getD i #[]).getD 0 "" ++ "|" ++ (parsed.getD i #[]).getD 1 ""
    unless previous < current do
      throwError "ecma262 census Q2 contract: rows {i} and {i + 1} are not strictly increasing in kind then id ({previous}, {current})"
  for (kindName, expected) in expectedKindCounts do
    let observed := parsed.foldl (fun acc fields => if fields.getD 0 "" == kindName then acc + 1 else acc) 0
    unless observed == expected do
      throwError "ecma262 census Q2 contract: {censusRelativePath} holds {observed} {kindName} row(s); the addendum freezes {expected}"
  -- The moved row, by byte range rather than by id alone.
  let some movedFields := parsed.find? (fun f => f.getD 1 "" == movedRowId)
    | throwError "ecma262 census Q2 contract: {censusRelativePath} has no row {movedRowId}"
  let startField := movedFields.getD 3 ""
  let endField := movedFields.getD 4 ""
  let digestField := movedFields.getD 5 ""
  if startField != toString movedRowSpanB then
    throwError "ecma262 census Q2 contract: {movedRowId} starts at {startField}; the addendum cites {movedRowSpanB}"
  if endField != toString movedRowSpanE then
    throwError "ecma262 census Q2 contract: {movedRowId} ends at {endField}; the addendum cites {movedRowSpanE}"
  if digestField != movedRowDigest then
    throwError "ecma262 census Q2 contract: {movedRowId} records span digest {digestField}; the addendum cites {movedRowDigest}"
  let recomputed := Gates.Sha256.hexDigest (bytes.extract movedRowSpanB movedRowSpanE)
  if recomputed != movedRowDigest then
    throwError "ecma262 census Q2 contract: the pinned bytes [{movedRowSpanB}, {movedRowSpanE}) hash to {recomputed}; the addendum cites {movedRowDigest} for {movedRowId}"
  -- The amended numerator scaffold.
  let rowsPath := projectRoot / rowsRelativePath
  unless ← liftIO rowsPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {rowsRelativePath}; run `{regenerateCommand}`"
  let rowsText ← liftIO <| IO.FS.readFile rowsPath
  let rowsLines := Gates.Common.lines rowsText
  unless rowsLines.contains s!"def rowTotal : Nat := {expectedRowTotal}" do
    throwError "ecma262 census Q2 contract: {rowsRelativePath} does not record rowTotal {expectedRowTotal}"
  unless rowsLines.contains s!"def denominator : Nat := {expectedDenominator}" do
    throwError "ecma262 census Q2 contract: {rowsRelativePath} does not record denominator {expectedDenominator}"
  for (dispositionName, expected) in expectedDispositionCounts do
    let observed := occurrencesOf rowsText (", ." ++ dispositionName ++ ",")
    unless observed == expected do
      throwError "ecma262 census Q2 contract: {rowsRelativePath} carries {observed} {dispositionName} row(s); the addendum freezes {expected}"
  for expectedLine in expectedRowsModuleLines do
    unless rowsLines.contains expectedLine do
      throwError "ecma262 census Q2 contract: {rowsRelativePath} does not carry the frozen entry {expectedLine}"
  -- Amendment 1.1's authored form: dispositions.tsv, never overrides.tsv.
  let overridesPath := projectRoot / overridesRelativePath
  unless ← liftIO overridesPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {overridesRelativePath}"
  let overrideEntries := Gates.Common.listFileEntries (← liftIO <| IO.FS.readFile overridesPath)
  let overrideRowIds := overrideEntries.map fun entry => (entry.splitOn "\t").headD entry
  unless overrideRowIds.length == expectedOverrideRowIds.length do
    throwError "ecma262 census Q2 contract: {overridesRelativePath} carries {overrideRowIds.length} override(s); the addendum freezes {expectedOverrideRowIds.length}"
  for rowId in expectedOverrideRowIds do
    unless overrideRowIds.contains rowId do
      throwError "ecma262 census Q2 contract: {overridesRelativePath} has no override for {rowId}"
  if overrideRowIds.contains movedRowId then
    throwError "ecma262 census Q2 contract: {overridesRelativePath} overrides {movedRowId}; amendment 1.1 is authored in census/ecma262/dispositions.tsv, because an override would leave the clause's own disposition line matching no row"
  -- Q2 acceptance 2, re-checked independently of Gates.Census.checkDependencies.
  -- This standard has an empty crossCensusPaths, so a target that is neither
  -- an in-census row id nor a declared external is a failure with no third case.
  let dependenciesPath := projectRoot / dependenciesRelativePath
  let externalsPath := projectRoot / externalsRelativePath
  unless ← liftIO dependenciesPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {dependenciesRelativePath}"
  unless ← liftIO externalsPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {externalsRelativePath}"
  let dependencyEntries := Gates.Common.listFileEntries (← liftIO <| IO.FS.readFile dependenciesPath)
  let externals := Gates.Common.listFileEntries (← liftIO <| IO.FS.readFile externalsPath)
  let censusRowIds := censusRowIdsOf censusText
  let mut owners : List String := []
  let mut usedExternals : List String := []
  for entry in dependencyEntries do
    match entry.splitOn "\t" with
    | [rowId, targetField] =>
      unless censusRowIds.contains rowId do
        throwError "ecma262 census Q2 contract: {dependenciesRelativePath} names {rowId}, which is not a row of {censusRelativePath}"
      if owners.contains rowId then
        throwError "ecma262 census Q2 contract: {dependenciesRelativePath} carries two lines for {rowId}"
      owners := rowId :: owners
      for target in dependencyTargets targetField do
        if target == rowId then
          throwError "ecma262 census Q2 contract: {dependenciesRelativePath} makes {rowId} depend on itself"
        if target.startsWith "ext." then
          unless externals.contains target do
            throwError "ecma262 census Q2 contract: {dependenciesRelativePath} names the undeclared external {target}"
          unless usedExternals.contains target do
            usedExternals := target :: usedExternals
        else
          unless censusRowIds.contains target do
            throwError "ecma262 census Q2 contract: {dependenciesRelativePath} names {target}, which is neither a row of this census nor a declared external"
    | _ =>
      throwError "ecma262 census Q2 contract: {dependenciesRelativePath} line `{entry}` is not two tab-separated fields"
  for rowId in censusRowIds do
    unless owners.contains rowId do
      throwError "ecma262 census Q2 contract: {dependenciesRelativePath} carries no line for the census row {rowId}"
  for identity in externals do
    unless usedExternals.contains identity do
      throwError "ecma262 census Q2 contract: {externalsRelativePath} declares {identity}, which no dependency line uses"
  -- Q2 acceptance 5: named, not duplicated.
  let scannerPath := projectRoot / scannerBatteryRelativePath
  unless ← liftIO scannerPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {scannerBatteryRelativePath}, which carries the real anchor-ladder probes"
  let scannerText ← liftIO <| IO.FS.readFile scannerPath
  for fragment in expectedScannerProbeFragments do
    unless occurrencesOf scannerText fragment > 0 do
      throwError "ecma262 census Q2 contract: {scannerBatteryRelativePath} no longer carries `{fragment}`; Q2 acceptance 5 rests on those probes running the real Gates.Census.chooseAnchorLength"
  -- Q2 acceptance 4: the numerator, the entry point and the emitted block.
  let numeratorPath := projectRoot / numeratorRelativePath
  unless ← liftIO numeratorPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {numeratorRelativePath}, the ES2026 coverage numerator the report is printed from"
  let numeratorText ← liftIO <| IO.FS.readFile numeratorPath
  for fragment in expectedNumeratorFragments do
    unless occurrencesOf numeratorText fragment > 0 do
      throwError "ecma262 census Q2 contract: {numeratorRelativePath} does not carry `{fragment}`"
  let entryPointPath := projectRoot / entryPointRelativePath
  unless ← liftIO entryPointPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {entryPointRelativePath}"
  let entryPointText ← liftIO <| IO.FS.readFile entryPointPath
  for fragment in expectedEntryPointFragments do
    unless occurrencesOf entryPointText fragment > 0 do
      throwError "ecma262 census Q2 contract: {entryPointRelativePath} does not carry `{fragment}`; the addendum freezes the standard-key-to-emit map"
  let coverageDocPath := projectRoot / coverageDocRelativePath
  unless ← liftIO coverageDocPath.pathExists do
    throwError "ecma262 census Q2 contract: missing {coverageDocRelativePath}"
  let coverageDocText ← liftIO <| IO.FS.readFile coverageDocPath
  unless occurrencesOf coverageDocText expectedCoverageBlock > 0 do
    throwError "ecma262 census Q2 contract: {coverageDocRelativePath} does not carry the all-absent ES2026 coverage block the Lean emit prints; the Q1 placeholder block is still there"
  logInfo
    m!"ecma262 census Q2 contract: {expectedRowTotal} rows, denominator {expectedDenominator}, {movedRowId} re-dispositioned owned against {sourceRelativePath} (SHA-256 {sourceDigest}), {overrideRowIds.length} overrides unchanged, {censusRowIds.length} dependency lines and {externals.length} externals used in both directions, and the all-absent coverage block emitted"

#ecma262_census_q2_gate

end WhatwgTest.Audit.Ecma262.CensusQ2Contract
