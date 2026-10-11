import WhatwgGates.Trust.Main
import WhatwgGates.TrustSelfTest

/-!
# Gates.TrustSelfTest.InProcess

The default run of the trust self-test (addendum V2g of
`test/contracts/trust-gate-hardening.contract.md`, ruling R-S6, debt D79): every
row of `WhatwgGates/TrustSelfTest.lean` judged in one process, with no build of
the tree for any of them.

## Why

The one-plant run (`--each`) copies the tree and, for each of 92 rows, runs
`lake build` in the copy and then the executable gate: about eighteen minutes.
The gate's own work in each of those is a few seconds; the rest is Lake, the
elaborator and the linker. This run calls the gate library directly.

## The planted view

A row's edits are applied to texts in memory (`Overlay`), by the functions the
one-plant run uses on its copy, so a missing or repeated anchor fails the row as
before. Nothing is written into the checkout. The gate library's run,
`Gates.Trust.runPassesOver`, takes the source list and a scan function, so it is
handed the audited sources with the planted texts in place; it is the run both
judges of the tree make. The host's reads are the executable's: the token table
rebuilt from raw parser entries, the raw scoped tokens, no root constants, and
its own axiom traversal. After it the harness calls the executable's other steps
that a plant can reach: step 0 over a planted `lakefile.toml`, and step 5, the
extension allowlist.

## How a row is judged

A row's `judgement` says which of five ways applies.

- `passes`. The run above over the planted texts, with the built environment as
  it stands. A list fixture is read with Lean's tokenizer and its entries are
  put at the head of the list its anchor names, so the configuration is a
  planted value.
- `compiled`. `lean` first compiles each planted module, with the loader's
  search path and the options the trace of module `Whatwg` records; rows that
  plant the same text at the same module share one compile. The environment is
  then the built tree with the plant imported. An acceptance row requires that
  `lean` accept the plant and that no pass have a finding.
- `leanRefuses`. `lean` must refuse the planted module, with the row's fragment
  where it has one; the executable's freshness step, over the planted source
  beside the module's built file and trace, must refuse it as the row's
  executable expectation says.
- `lakeOptions`. Lake builds a package of one empty module `Whatwg` whose
  `lakefile.toml` is the package table and the `Whatwg` library table of the
  planted one; the executable's recorded-options step reads the trace Lake
  wrote. The same package with no plant is a control.
- `freshness`. The freshness step over a directory that holds the row's module
  as its edits leave it: source, trace and built file.

## One import

`Lean.importModulesCore` keeps its state. The harness imports the tree once,
keeps that state, and for each compiled row resumes from it with the plant's
built file given by path, so only the plant is read. A second full import in one
process would copy every built file: the first holds each mapped at its base
address. A plant appended to an existing module replaces that module, so such a
row resumes from an earlier state, taken before the replaced modules and their
importers were loaded.

## The in-tree command

The judge above is the library with the executable's reads. The in-tree command
`#whatwg_streams_axiom_gate` adds two things only an elaborating process has: the
constants the root has declared, and the check that its own elaborator ran the
command. A row whose `inTreeOnly` names a fragment that comes from one of them
gets a second judgement: `lean` elaborates the planted root, with the audited
sources copied beside it and the built tree on its search path, and must print
that fragment. On the unmodified tree the narrow run of the command and
`lake exe whatwg_trustgate` must both print the summary this run computed.

## What it does not show

Section V2g.6 of the contract. In particular the in-tree command judges two
planted trees and not ninety, and a text row's plant is not elaborated. `--each`
shows both.
-/

namespace Gates.TrustSelfTest.InProcess

open Lean
open Gates.Common

/-! ## Planted texts -/

/-- The files one row plants, by path under the project root: the text of a
file it writes, or `none` for a file it removes. Nothing here is on disk. -/
structure Overlay where
  entries : Array (System.FilePath × Option String) := #[]

/-- What the row planted at `path`, if anything. -/
def Overlay.find? (overlay : Overlay) (path : System.FilePath) : Option (Option String) :=
  (overlay.entries.find? fun entry => Trust.pathKey entry.1 == Trust.pathKey path).map (·.2)

/-- The overlay with `path` planted as `text`. -/
def Overlay.set (overlay : Overlay) (path : System.FilePath) (text : Option String) : Overlay :=
  let key := Trust.pathKey path
  if overlay.entries.any fun entry => Trust.pathKey entry.1 == key then
    { entries := overlay.entries.map fun entry =>
        if Trust.pathKey entry.1 == key then (entry.1, text) else entry }
  else
    { entries := overlay.entries.push (path, text) }

/-- The text of `path` as the row has left it: the planted text, or the file on
disk; `none` when the row removed it or it does not exist. -/
def currentText (overlay : Overlay) (path : System.FilePath) : IO (Option String) := do
  match overlay.find? path with
  | some planted => return planted
  | none =>
      if ← path.pathExists then
        return some (← IO.FS.readFile path)
      return none

/-- Whether `path` exists as the row has left it. The file is not read: a row may
remove a built file, which is no text. -/
def currentlyExists (overlay : Overlay) (path : System.FilePath) : IO Bool := do
  match overlay.find? path with
  | some planted => return planted.isSome
  | none => path.pathExists

/-- One edit, made in the overlay as `Edit.apply` makes it in the probe copy. An
edit that cannot be made throws, and fails its row. -/
def plantEdit (root : System.FilePath) (overlay : Overlay) (edit : Edit) : IO Overlay := do
  let path := edit.target root
  let present ← currentlyExists overlay path
  let mustExist : IO String := do
    match ← (if present then currentText overlay path else pure none) with
    | some text => pure text
    | none => throw <| IO.userError s!"{path} does not exist; this edit needs it"
  let planted : IO String := IO.FS.readFile (fixture root edit.fixtureName)
  match edit.placement with
  | .append =>
      return overlay.set path (some ((← mustExist) ++ "\n" ++ (← planted)))
  | .afterAnchor anchor =>
      match insertAfterAnchor (← mustExist) anchor (← planted) with
      | .ok text => return overlay.set path (some text)
      | .error message => throw <| IO.userError s!"{path}: {message}"
  | .newModule =>
      if present then
        throw <| IO.userError s!"{path} already exists; a planted module must be new"
      let moduleName ← moduleNameOf root path
      let rootPath := testRoot root
      let some rootText ← currentText overlay rootPath
        | throw <| IO.userError s!"{rootPath} does not exist"
      return (overlay.set path (some (← planted))).set rootPath
        (some (s!"import {moduleName}\n" ++ rootText))
  | .reelaborate =>
      return overlay.set path
        (some ((← mustExist) ++ "\n-- trust self-test: re-elaborate this module\n"))
  | .beforeRootGate =>
      match insertBeforeLine (← mustExist) rootGateCommand (← planted) with
      | .ok text => return overlay.set path (some text)
      | .error message => throw <| IO.userError s!"{path}: {message}"
  | .newFile =>
      if present then
        throw <| IO.userError s!"{path} already exists; a planted file must be new"
      return overlay.set path (some (← planted))
  | .remove =>
      unless present do
        throw <| IO.userError s!"{path} does not exist; a removed file must exist"
      return overlay.set path none

/-- Every edit of a row, in order. -/
def plantEdits (root : System.FilePath) (edits : List Edit) : IO Overlay := do
  let mut overlay : Overlay := {}
  for edit in edits do
    overlay ← plantEdit root overlay edit
  return overlay

/-! ## Planted configuration -/

/-- One entry of a list fixture, `⟨name, "reason"⟩ ::`, whose first field is a
name literal or, for the extension allowlist, a string literal. -/
structure ListEntry where
  name? : Option Name := none
  text? : Option String := none
  reason : String

/-- The entries of a list fixture, read with Lean's tokenizer. A fixture is one
or more entries and nothing else. -/
def listEntries (environment : Environment) (tokenTable : Parser.TokenTable)
    (fixtureName text : String) : Except String (Array ListEntry) := do
  let (tokens, failure?) := Trust.foldCodeTokens environment tokenTable fixtureName text
    (#[] : Array Syntax) fun tokens token _ => tokens.push token
  if let some failure := failure? then
    throw failure
  let mut entries : Array ListEntry := #[]
  let mut index := 0
  for _ in [0:tokens.size] do
    if index ≥ tokens.size then
      break
    let tokenAt (offset : Nat) : Syntax := tokens[index + offset]?.getD .missing
    unless (tokenAt 0).isToken "⟨" && (tokenAt 2).isToken "," && (tokenAt 4).isToken "⟩" &&
        (tokenAt 5).isToken "::" do
      throw s!"{fixtureName}: token {index} does not open an entry of the form ⟨name, \"reason\"⟩ ::"
    let some reason := (tokenAt 3).isStrLit?
      | throw s!"{fixtureName}: the reason of the entry at token {index} is not a string literal"
    match (tokenAt 1).isNameLit?, (tokenAt 1).isStrLit? with
    | some name, _ => entries := entries.push { name? := some name, reason }
    | none, some named => entries := entries.push { text? := some named, reason }
    | none, none =>
        throw s!"{fixtureName}: the entry at token {index} names neither a name literal nor a string literal"
    index := index + 6
  if entries.isEmpty then
    throw s!"{fixtureName}: the fixture holds no list entry"
  return entries

/-- The names of entries that must each carry a name literal. -/
def entryNames (fixtureName : String) (entries : Array ListEntry) :
    Except String (List (Name × String)) :=
  entries.toList.mapM fun entry =>
    match entry.name? with
    | some name => pure (name, entry.reason)
    | none => throw s!"{fixtureName}: an entry of this list is named by a name literal"

/-- `base` with a fixture's entries at the head of the list its anchor names, as
the fixture's text inserted after that anchor in the configuration module puts
them. -/
def withListEntries (base : Trust.Config) (anchor fixtureName : String)
    (entries : Array ListEntry) : Except String Trust.Config := do
  if anchor == strictExceptionAnchor then
    let planted := (← entryNames fixtureName entries).map fun (declaration, reason) =>
      ({ declaration, reason } : Trust.StrictCeilingException)
    return { base with strictCeilingExceptions := planted ++ base.strictCeilingExceptions }
  if anchor == tokenExemptionAnchor then
    let planted := (← entryNames fixtureName entries).map fun (moduleName, reason) =>
      ({ moduleName, reason } : Trust.SourceTokenExemption)
    return { base with sourceTokenExemptions := planted ++ base.sourceTokenExemptions }
  if anchor == metaprogrammingModuleAnchor then
    let planted := (← entryNames fixtureName entries).map fun (moduleName, reason) =>
      ({ moduleName, reason } : Trust.MetaprogrammingModule)
    return { base with metaprogrammingModules := planted ++ base.metaprogrammingModules }
  if anchor == extensionAllowlistAnchor then
    let planted ← entries.toList.mapM fun entry =>
      match entry.text? with
      | some extension =>
          pure ({ extension, reason := entry.reason } : Trust.ExtensionAllowlistEntry)
      | none => throw s!"{fixtureName}: an allowlist entry is named by a string literal"
    return { base with extensionAllowlist := planted ++ base.extensionAllowlist }
  throw s!"{fixtureName}: the anchor `{anchor}` names no list of the configuration"

/-! ## Rows -/

/-- What a row requires. -/
inductive Wanted where
  /-- An acceptance row: `lean` accepts the plant and no pass has a finding. -/
  | acceptance
  /-- A rejection row: one of `fragments` for the in-tree command (any refusal
  when there is none), and the executable's own expectation. -/
  | rejection (fragments : List String) (executable : ExecutableExpectation)
  /-- A row the executable alone judges. -/
  | executableOnly (expectation : ExecutableExpectation)

/-- One row of any table, as this run reads it. -/
structure Row where
  label : String
  judgement : Judgement
  /-- The edits the one-plant run makes before its build. -/
  edits : List Edit
  /-- The edits it makes after the build. -/
  afterBuild : List Edit := []
  wanted : Wanted
  /-- The fragments the in-tree command alone prints; see `Plant.inTreeOnly`. -/
  inTreeOnly : List String := []

def acceptanceRow (plant : Plant) : Row :=
  { label := plant.label, judgement := plant.judgement, edits := plant.edits,
    wanted := .acceptance }

def rejectionRow (plant : Plant) : Row :=
  { label := plant.label, judgement := plant.judgement, edits := plant.edits,
    wanted := .rejection plant.expected (plant.executable.getD (.refusesAny plant.expected)),
    inTreeOnly := plant.inTreeOnly }

def executableRow (plant : ExecutablePlant) : Row :=
  { label := plant.label, judgement := plant.judgement, edits := plant.edits,
    afterBuild := plant.afterBuild, wanted := .executableOnly plant.expectation }

/-- The module-closure row: a new source the root does not import. -/
def unreachableRow : Row :=
  { label := unreachableLabel, judgement := .passes,
    edits := [{ target := unreachableSource, fixtureName := "unreachable.lean.txt",
                placement := .newFile }],
    wanted := .rejection unreachableFragments (.refusesAny unreachableFragments) }

/-- Every planted row, in the order of the one-plant run. -/
def plantedRows : List Row :=
  acceptancePlants.map acceptanceRow ++ rejectionPlants.map rejectionRow ++ [unreachableRow] ++
    executablePlants.map executableRow

/-- Whether an edit targets the configuration module. -/
def editsConfiguration (root : System.FilePath) (edit : Edit) : Bool :=
  Trust.pathKey (edit.target root) == Trust.pathKey (trustConfigSource root)

/-- A row's class (addendum V2g.2), as its lines print it. -/
def className (root : System.FilePath) (row : Row) : String :=
  let configuration := (row.edits ++ row.afterBuild).any (editsConfiguration root)
  match row.judgement with
  | .passes => if configuration then "configuration data" else "text"
  | .compiled =>
      if configuration then "configuration data over a compiled plant" else "compiled plant"
  | .leanRefuses => "real build: lean's refusal and the freshness step"
  | .lakeOptions => "real build: a one-module package"
  | .freshness => "real build: the freshness step over an edited build"

/-! ## Compiling a plant -/

/-- One planted module to compile: its module name and its text. -/
structure CompileJob where
  moduleName : Name
  text : String
  /-- The directory the job writes in, outside the checkout. -/
  directory : System.FilePath

def CompileJob.source (job : CompileJob) : System.FilePath :=
  Lean.modToFilePath job.directory job.moduleName "lean"

def CompileJob.olean (job : CompileJob) : System.FilePath :=
  job.directory / "plant.olean"

/-- How one `lean` run ended. -/
structure CompileResult where
  exitCode : UInt32
  output : String
  milliseconds : Nat

/-- What a row's judgement needs beside its edits. -/
structure Planned where
  row : Row
  /-- Every edit of the row, the after-build ones included. -/
  overlay : Overlay
  /-- The planted module sources `lean` compiles for the row, by job index. -/
  jobs : Array Nat := #[]
  /-- The planted module sources `lean` compiles for the row's in-tree twin. -/
  inTreeJobs : Array Nat := #[]

/-- The planted module sources of an overlay that a build of the tree would
compile into the environment: a source under an audited tree or one of the two
imported roots. The test root and the entry points are never imported, and the
configuration module is planted as a value. -/
def plantedModules (root : System.FilePath) (overlay : Overlay) :
    IO (Array (Name × String)) := do
  let mut found : Array (Name × String) := #[]
  for (path, planted) in overlay.entries do
    let some text := planted | continue
    unless Trust.isLeanSourceName path do continue
    let key := Trust.pathKey path
    if key == Trust.pathKey (testRoot root) || key == Trust.pathKey (trustConfigSource root) then
      continue
    let relative ← relativeTo root path
    if relative.startsWith "whatwgbin/" then continue
    found := found.push ((← moduleNameOf root path).toName, text)
  return found

/-! ## The run's state -/

/-- What the whole run shares. -/
structure Run where
  root : System.FilePath
  /-- A throwaway directory outside the checkout. -/
  scratch : System.FilePath
  counter : IO.Ref Nat
  base : Trust.Config
  /-- The audited sources on disk. -/
  sources : Trust.AuditedSources
  /-- The modules some row replaces, and every module that imports one. -/
  replaced : NameSet
  /-- The import state before any module of `replaced` was loaded. -/
  earlyState : ImportState
  /-- The import state of the whole built tree. -/
  baseState : ImportState
  /-- The built tree, imported with no extension loaded. -/
  environment : Environment
  reads : Trust.HostReads
  /-- The built tree's token table, sorted. -/
  tokens : Array String
  /-- The scan of every source on disk, by path key. -/
  scans : Std.HashMap String Trust.SourceScan
  /-- The axioms of every constant the built tree's traversal closed. -/
  memo : Std.HashMap Name (Array Name)
  /-- `memo` without the constants of the modules of `replaced`. -/
  memoWithoutReplaced : Std.HashMap Name (Array Name)
  leanExecutable : System.FilePath
  leanPath : String
  /-- The `-D` options Lake compiles a module of the package with. -/
  leanOptions : Array String

/-- A new directory under the scratch directory. -/
def Run.newDirectory (run : Run) (kind : String) : IO System.FilePath := do
  let index ← run.counter.modifyGet fun index => (index, index + 1)
  let directory := run.scratch / s!"{kind}-{index}"
  IO.FS.createDirAll directory
  return directory

/-- The tokens of a table, sorted, so that two tables can be compared. -/
def sortedTokens (table : Parser.TokenTable) : Array String :=
  table.values.qsort (· < ·)

/-- The modules a source text's header imports, each once and in order, read
with Lean's header parser as `Gates.Trust.headerImports` reads a file. -/
def headerImportsOfText (text fileName : String) : IO (Array Import) := do
  let (imports, _, messages) ← Elab.parseImports text (some fileName)
  if messages.hasErrors then
    throw <| IO.userError s!"the header of {fileName} does not parse"
  let mut modules : Array Name := #[]
  for entry in imports do
    unless modules.contains entry.module do
      modules := modules.push entry.module
  return modules.map fun moduleName => { module := moduleName }

/-- Every module that is in `targets` or imports, directly or through other
modules, one that is. `importsOf` gives each audited module's own imports. -/
def importersOf (importsOf : Array (Name × Array Name)) (targets : NameSet) : NameSet := Id.run do
  let mut found := targets
  for _ in [0:importsOf.size + 1] do
    let mut grew := false
    for (moduleName, imports) in importsOf do
      if !found.contains moduleName && imports.any found.contains then
        found := found.insert moduleName
        grew := true
    unless grew do
      break
  return found

/-! ## Environments -/

/-- The built tree with a row's compiled plants imported: the import of the
planted root's import set, resumed from a state that already holds every module
the row does not replace, with each plant's built file given by path. -/
def importPlanted (run : Run) (rootText : String) (compiled : Array (Name × System.FilePath)) :
    IO Environment := do
  let imports ← headerImportsOfText rootText "WhatwgTest.lean"
  let arts : NameMap ImportArtifacts := compiled.foldl (init := {}) fun arts (moduleName, olean) =>
    arts.insert moduleName (.ofArrays #[#[olean]])
  let replaces := compiled.any fun (moduleName, _) => run.replaced.contains moduleName
  for (moduleName, _) in compiled do
    if run.environment.header.moduleNames.contains moduleName &&
        !run.replaced.contains moduleName then
      throw <| IO.userError s!"module {moduleName} is replaced by a plant the run did not plan for"
  let start := if replaces then run.earlyState else run.baseState
  withImporting do
    let (_, state) ← (importModulesCore imports (arts := arts)).run start
    finalizeImport state imports {} 0 (leakEnv := false) (loadExts := false)

/-! ## The gate's run over a planted view -/

/-- The audited sources with a row's new files added. -/
def plantedSources (run : Run) (overlay : Overlay) : IO Trust.AuditedSources := do
  let known := (run.sources.modules ++ run.sources.entryPoints).map Trust.pathKey
  let mut modules := run.sources.modules
  let mut entryPoints := run.sources.entryPoints
  for (path, planted) in overlay.entries do
    if planted.isNone || !Trust.isLeanSourceName path || known.contains (Trust.pathKey path) then
      continue
    let relative ← relativeTo run.root path
    if relative.startsWith "whatwgbin/" then
      entryPoints := entryPoints.push path
    else if relative.startsWith "Whatwg/" || relative.startsWith "WhatwgTest/" ||
        relative.startsWith "WhatwgGates/" then
      modules := modules.push path
  return { modules, entryPoints }

/-- Every finding of the executable's steps a plant can reach, over one planted
view, in order: step 0 when the row plants `lakefile.toml`; the gate library's
run with the executable's reads; step 5, the extension allowlist. The summary is
returned only when there is no finding. `planted` says the environment is not
the built tree's own, and `replaces` that the row replaced a module of it. -/
def gateFindings (run : Run) (config : Trust.Config) (overlay : Overlay)
    (environment : Environment) (planted replaces : Bool) :
    IO (Array String × Option Trust.Summary) := do
  let mut findings : Array String := #[]
  if let some (some lakefileText) := overlay.find? (lakefileSource run.root) then
    let directory ← run.newDirectory "lakefile"
    IO.FS.writeFile (directory / "lakefile.toml") lakefileText
    findings := findings ++ (← Trust.buildConfigurationFindings directory)
  let reads : Trust.HostReads ←
    if planted then
      pure { tokenTable := ← Trust.rebuiltTokenTable environment
             scopedTokens := Trust.rawScopedTokens environment
             rootConstants := #[] }
    else
      pure run.reads
  -- A scan made with the built tree's table stands only under that table.
  let sameTable := !planted || sortedTokens reads.tokenTable == run.tokens
  let scan : System.FilePath → IO Trust.SourceScan := fun source => do
    match overlay.find? source with
    | some (some text) => return Trust.scanSourceText environment reads.tokenTable source text
    | some none => throw <| IO.userError s!"{source} is an audited source the row removed"
    | none =>
        match (if sameTable then run.scans[Trust.pathKey source]? else none) with
        | some found => return found
        | none => Trust.scanSource environment reads.tokenTable source
  let memo ← IO.mkRef (if replaces then run.memoWithoutReplaced else run.memo)
  let exhausted ← IO.mkRef (#[] : Array String)
  let axiomsOf : Name → IO (Array Name) := fun name => do
    let result := Trust.traverseAxioms environment Trust.axiomTraversalFuel (← memo.swap {}) name
    memo.set result.memo
    match result.axioms? with
    | some axioms => return axioms
    | none =>
        exhausted.modify (·.push
          s!"Whatwg axiom gate: the axiom traversal of {name} exhausted its fuel of {Trust.axiomTraversalFuel} steps")
        return #[]
  -- Every audited declaration first and in order, as the executable asks, so
  -- that no pass's order of questions changes an answer.
  match Trust.auditedDeclarations config environment with
  | .ok declarations =>
      for declaration in declarations do
        discard <| axiomsOf declaration.name
  | .error message => throw <| IO.userError message
  let collected ← IO.mkRef (#[] : Array String)
  let host : Trust.Host IO :=
    { axiomsOf, report := fun found => collected.modify (· ++ found) }
  let rootFile := testRoot run.root
  let some rootText ← currentText overlay rootFile
    | throw <| IO.userError s!"{rootFile} does not exist"
  let sources ← plantedSources run overlay
  let summary? ←
    match ← (Trust.runPassesOver config host environment reads run.root sources scan rootFile
        rootText).run with
    | .ok summary? => pure summary?
    | .error message => throw <| IO.userError message
  findings := findings ++ (← collected.get) ++ (← exhausted.get)
  findings := findings ++ Trust.allowlistFindings config environment
  return (findings, if findings.isEmpty then summary? else none)

/-! ## Expectations -/

/-- Whether some finding holds the fragment. -/
def holdsIn (findings : Array String) (fragment : String) : Bool :=
  findings.any fun finding => (finding.splitOn fragment).length > 1

/-- Whether findings meet an expectation: what a `PASS` line says of it, or why
they do not. -/
def meets (findings : Array String) : ExecutableExpectation → Except String String
  | .accepts =>
      if findings.isEmpty then .ok "" else .error "no finding was expected"
  | .refusesAny [] =>
      if findings.isEmpty then .error "a finding was expected and there is none" else .ok ""
  | .refusesAny fragments =>
      match fragments.find? (holdsIn findings) with
      | some fragment => .ok s!" with the expected diagnostic: {fragment}"
      | none => .error s!"expected one of: {fragments}"
  | .refusesAll fragments =>
      let missing := fragments.filter (!holdsIn findings ·)
      if missing.isEmpty then .ok s!" with every expected diagnostic: {fragments}"
      else .error s!"expected every one of: {fragments}; missing: {missing}"

/-- How one row ended: its lines for standard output and for standard error. -/
structure Outcome where
  label : String
  ok : Bool
  className : String
  out : Array String := #[]
  err : Array String := #[]
  milliseconds : Nat := 0

/-- A failed row: one `FAIL` line and the detail under it. -/
def failed (root : System.FilePath) (row : Row) (reason : String) (detail : Array String := #[]) :
    Outcome :=
  { label := row.label, ok := false, className := className root row,
    err := #[s!"FAIL {reason}"] ++ detail.map fun line => s!"  {line}" }

/-- A row that passed, with its one line. -/
def passed (root : System.FilePath) (row : Row) (line : String) : Outcome :=
  { label := row.label, ok := true, className := className root row,
    out := #[s!"PASS {line} [in process: {className root row}]"] }

/-- Judge findings against what a row wants. -/
def judgeFindings (root : System.FilePath) (row : Row) (findings : Array String)
    (summary? : Option Trust.Summary) : Outcome :=
  match row.wanted with
  | .acceptance =>
      if !findings.isEmpty then
        failed root row s!"trust gate unexpectedly rejected {row.label}" findings
      else
        match summary? with
        | some summary =>
            if templateMatches gateSummaryTemplate summary.line then
              passed root row s!"trust gate accepted {row.label}"
            else
              failed root row
                s!"trust gate accepted {row.label}, but its summary does not match the template: {summary.line}"
        | none => failed root row s!"trust gate accepted {row.label} and returned no summary"
  | .rejection fragments executable =>
      match meets findings (.refusesAny fragments), meets findings executable with
      | .ok said, .ok _ => passed root row s!"planted {row.label} rejected{said}"
      | .error reason, _ =>
          if findings.isEmpty then
            failed root row s!"trust gate unexpectedly accepted {row.label}"
          else
            failed root row
              s!"trust gate rejected {row.label} for an unexpected reason; {reason}" findings
      | _, .error reason =>
          failed root row
            s!"executable gate did not meet its expectation for {row.label}; {reason}" findings
  | .executableOnly expectation =>
      match meets findings expectation with
      | .ok said => passed root row s!"executable gate refused {row.label}{said}"
      | .error reason =>
          if findings.isEmpty then
            failed root row s!"executable gate unexpectedly accepted {row.label}"
          else
            failed root row
              s!"executable gate refused {row.label} for an unexpected reason; {reason}" findings

/-! ## Judging one row -/

/-- The configuration a row plants: the base value with each list fixture's
entries at the head of the list its anchor names. -/
def plantedConfiguration (run : Run) (row : Row) : IO Trust.Config := do
  let mut config := run.base
  for edit in row.edits ++ row.afterBuild do
    unless editsConfiguration run.root edit do continue
    let .afterAnchor anchor := edit.placement
      | throw <| IO.userError "an edit of the configuration module is not an after-anchor edit"
    let text ← IO.FS.readFile (fixture run.root edit.fixtureName)
    let planted := do
      let entries ← listEntries run.environment run.reads.tokenTable edit.fixtureName text
      withListEntries config anchor edit.fixtureName entries
    match planted with
    | .ok next => config := next
    | .error message => throw <| IO.userError message
  return config

/-- The last lines of a `lean` or `lake` run, for a `FAIL` line's detail. -/
def lastLines (output : String) (count : Nat := 20) : Array String :=
  ((lines output).reverse.take count).reverse.toArray

/-- A `passes` or `compiled` row: the gate's run over its planted view. -/
def judgeByRun (run : Run) (planned : Planned) (jobs : Array CompileJob)
    (results : Array (Option (Except IO.Error CompileResult))) : IO Outcome := do
  let row := planned.row
  let config ← plantedConfiguration run row
  let mut compiled : Array (Name × System.FilePath) := #[]
  for index in planned.jobs do
    let some job := jobs[index]? | throw <| IO.userError s!"compile job {index} does not exist"
    match results[index]?.join with
    | some (.ok result) =>
        if result.exitCode != 0 then
          return failed run.root row
            s!"lean did not accept the plant of {row.label}: module {job.moduleName}, exit code {result.exitCode}"
            (lastLines result.output)
        compiled := compiled.push (job.moduleName, job.olean)
    | some (.error error) =>
        return failed run.root row s!"could not run lean for {row.label}: {error}"
    | none => return failed run.root row s!"the plant of {row.label} was not compiled"
  -- Two rows this judgement cannot carry. An acceptance says that Lean accepts
  -- the plant, which only a compile shows. A rejection with no fragment is met
  -- by any finding, and a new module that is not compiled already has one: the
  -- built environment does not hold it, so the closure pass reports its source.
  match row.wanted with
  | .acceptance =>
      if compiled.isEmpty then
        return failed run.root row
          s!"{row.label} is an acceptance row with no compiled plant; its judgement must be `compiled`"
  | .rejection [] _ =>
      if row.judgement == .passes then
        return failed run.root row
          s!"{row.label} names no fragment, so it cannot be judged on its text; its judgement must not be `passes`"
  | _ => pure ()
  let (findings, summary?) ←
    if compiled.isEmpty then
      gateFindings run config planned.overlay run.environment false false
    else
      let some rootText ← currentText planned.overlay (testRoot run.root)
        | throw <| IO.userError "the test root does not exist"
      let environment ← importPlanted run rootText compiled
      let replaces := compiled.any fun (moduleName, _) => run.replaced.contains moduleName
      gateFindings run config planned.overlay environment true replaces
  return judgeFindings run.root row findings summary?

/-- The freshness step over a directory that holds each module as given: its
source, planted or as it is on disk; its trace; and its built file unless the
row removed it. -/
def freshnessOver (run : Run) (modules : Array (Name × Option String × Bool)) :
    IO (Array String) := do
  let directory ← run.newDirectory "freshness"
  let realBuild := Trust.leanBuildDir run.root
  let plantedBuild := Trust.leanBuildDir directory
  for (moduleName, planted, keepsBuilt) in modules do
    let source := Lean.modToFilePath directory moduleName "lean"
    if let some parent := source.parent then IO.FS.createDirAll parent
    match planted with
    | some text => IO.FS.writeFile source text
    | none =>
        IO.FS.writeBinFile source
          (← IO.FS.readBinFile (Lean.modToFilePath run.root moduleName "lean"))
    let trace := Lean.modToFilePath plantedBuild moduleName "trace"
    if let some parent := trace.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile trace
      (← IO.FS.readBinFile (Lean.modToFilePath realBuild moduleName "trace"))
    if keepsBuilt then
      IO.FS.writeBinFile (Lean.modToFilePath plantedBuild moduleName "olean")
        (← IO.FS.readBinFile (Lean.modToFilePath realBuild moduleName "olean"))
  Trust.freshnessFindings directory (modules.map (·.1))

/-- A `leanRefuses` row: `lean` refuses the planted module, and the freshness
step refuses the edited source. -/
def judgeLeanRefusal (run : Run) (planned : Planned) (jobs : Array CompileJob)
    (results : Array (Option (Except IO.Error CompileResult))) : IO Outcome := do
  let row := planned.row
  let .rejection fragments executable := row.wanted
    | return failed run.root row s!"{row.label} is not a rejection row"
  let mut said := ""
  let mut stale : Array (Name × Option String × Bool) := #[]
  for index in planned.jobs do
    let some job := jobs[index]? | throw <| IO.userError s!"compile job {index} does not exist"
    match results[index]?.join with
    | some (.ok result) =>
        if result.exitCode == 0 then
          return failed run.root row s!"lean unexpectedly accepted the plant of {row.label}"
        match fragments with
        | [] => said := "lean refused the planted module"
        | _ =>
            match fragments.find? fun fragment => (result.output.splitOn fragment).length > 1 with
            | some fragment =>
                said := s!"lean refused the planted module with the expected diagnostic: {fragment}"
            | none =>
                return failed run.root row
                  s!"lean refused {row.label} for an unexpected reason; expected one of: {fragments}"
                  (lastLines result.output)
        stale := stale.push (job.moduleName, some job.text, true)
    | some (.error error) =>
        return failed run.root row s!"could not run lean for {row.label}: {error}"
    | none => return failed run.root row s!"the plant of {row.label} was not compiled"
  if stale.isEmpty then
    return failed run.root row s!"{row.label} plants no module for lean to refuse"
  let findings ← freshnessOver run stale
  match meets findings executable with
  | .ok fresh =>
      return passed run.root row
        s!"planted {row.label} rejected: {said}, and the freshness step refused the edited source{fresh}"
  | .error reason =>
      return failed run.root row
        s!"the freshness step did not meet the executable's expectation for {row.label}; {reason}"
        findings

/-- The module a built file under the build directory belongs to. -/
def builtModule? (root path : System.FilePath) : IO (Option Name) := do
  let build := forwardSlashes (Trust.leanBuildDir root).toString ++ "/"
  let spelled := forwardSlashes path.toString
  unless spelled.startsWith build && spelled.endsWith ".olean" do
    return none
  let inner := dropLastChars (dropChars spelled build.length) 6
  return some (String.intercalate "." (inner.splitOn "/")).toName

/-- A `freshness` row: the freshness step over the module its after-build edits
touch, as they leave it. -/
def judgeFreshness (run : Run) (planned : Planned) : IO Outcome := do
  let row := planned.row
  let .executableOnly _ := row.wanted
    | return failed run.root row s!"{row.label} is not an executable-only row"
  let mut modules : Array (Name × Option String × Bool) := #[]
  for (path, planted) in planned.overlay.entries do
    match ← builtModule? run.root path with
    | some moduleName =>
        if planted.isSome then
          return failed run.root row s!"{row.label} rewrites a built file; only its removal is judged"
        modules := modules.push (moduleName, none, false)
    | none =>
        let some text := planted
          | return failed run.root row s!"{row.label} removes {path}, which is no built file"
        modules := modules.push ((← moduleNameOf run.root path).toName, some text, true)
  if modules.isEmpty then
    return failed run.root row s!"{row.label} edits nothing after the build"
  let findings ← freshnessOver run modules
  return judgeFindings run.root row findings none

/-! ## The one-module package of the build-option rows -/

/-- The keys of the package table that decide how Lake compiles a module. -/
def packageCompileKeys : List String :=
  ["name", "leanOptions", "moreLeanArgs", "weakLeanArgs"]

/-- The key a `lakefile.toml` line sets, if it sets one. -/
def tomlKey? (line : String) : Option String :=
  match (trimmed line).splitOn "=" with
  | key :: _ :: _ => some (trimmed key)
  | _ => none

/-- A `lakefile.toml` reduced to what decides how the umbrella module is
compiled: the package table's name and compile options, and the whole table of
the library `Whatwg`, which is the table that holds the one line `anchor`. The
requirements, the other libraries and the executables are left out, so that the
package builds alone. -/
def reducedLakefile (text : String) (anchor : String := lakefileUmbrellaAnchor) :
    Except String String := do
  let all := (lines text).toArray
  let opensTable (line : String) : Bool := (trimmed line).startsWith "["
  let anchors := (all.filter fun line => trimmed line == anchor).size
  if anchors != 1 then
    throw s!"the anchor line `{anchor}` occurs {anchors} time(s) in lakefile.toml; exactly one is required"
  let some anchorIndex := all.findIdx? fun line => trimmed line == anchor
    | throw "the anchor line is missing"
  let firstTable := (all.findIdx? opensTable).getD all.size
  let packageLines := (all.extract 0 firstTable).filter fun line =>
    match tomlKey? line with
    | some key => packageCompileKeys.contains key
    | none => false
  let mut tableStart := anchorIndex
  for _ in [0:anchorIndex + 1] do
    if opensTable (all[tableStart]?.getD "") then
      break
    if tableStart == 0 then
      throw "the anchor line is in no table of lakefile.toml"
    tableStart := tableStart - 1
  let mut tableEnd := anchorIndex + 1
  for _ in [0:all.size] do
    if tableEnd ≥ all.size || opensTable (all[tableEnd]?.getD "") then
      break
    tableEnd := tableEnd + 1
  return String.intercalate "\n"
    (packageLines.toList ++ [""] ++ (all.extract tableStart tableEnd).toList) ++ "\n"

/-- How one build of the one-module package ended: Lake's exit code and output,
and the findings of the executable's freshness and recorded-options steps over
what it built. -/
structure PackageResult where
  exitCode : UInt32
  output : String
  freshness : Array String
  options : Array String
  milliseconds : Nat

/-- Build the one-module package for a `lakefile.toml` text and read its trace
with the executable's steps 1 and 2. -/
def buildPackage (run : Run) (lakefileText : String) : IO PackageResult := do
  let started ← IO.monoMsNow
  let reduced ← match reducedLakefile lakefileText with
    | .ok reduced => pure reduced
    | .error message => throw <| IO.userError message
  let directory ← run.newDirectory "package"
  IO.FS.writeFile (directory / "lakefile.toml") reduced
  IO.FS.writeBinFile (directory / "lean-toolchain")
    (← IO.FS.readBinFile (run.root / "lean-toolchain"))
  IO.FS.writeFile (directory / "Whatwg.lean")
    "-- trust self-test: the one module of the reduced package\n"
  let output ← IO.Process.output
    { cmd := lakeCommand, args := #["build", "Whatwg"], cwd := some directory }
  let text := output.stdout ++ output.stderr
  if output.exitCode != 0 then
    return { exitCode := output.exitCode, output := text, freshness := #[], options := #[],
             milliseconds := (← IO.monoMsNow) - started }
  let modules : Array Name := #[`Whatwg]
  let freshness ← Trust.freshnessFindings directory modules
  let options ← Trust.optionFindings directory modules
  return { exitCode := 0, output := text, freshness, options,
           milliseconds := (← IO.monoMsNow) - started }

/-- A `lakeOptions` row, judged on the build of its package. -/
def judgePackage (root : System.FilePath) (row : Row) (result : Except IO.Error PackageResult) :
    Outcome :=
  match result with
  | .error error => failed root row s!"could not build the package of {row.label}: {error}"
  | .ok built =>
      if built.exitCode != 0 then
        failed root row
          s!"lake did not build the package of {row.label}: exit code {built.exitCode}"
          (lastLines built.output)
      else if !built.freshness.isEmpty then
        failed root row s!"the package of {row.label} is not fresh after its build" built.freshness
      else
        judgeFindings root row built.options none

/-! ## Processes beside the judging -/

/-- Run every action, at most `width` at a time, and return each one's result
in order. -/
def runPool {α : Type} (width : Nat) (actions : Array (IO α)) :
    IO (Array (Option (Except IO.Error α))) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate actions.size (none : Option (Except IO.Error α)))
  let worker : IO Unit := do
    for _ in [0:actions.size] do
      let index ← next.modifyGet fun index => (index, index + 1)
      let some action := actions[index]? | break
      let result ← action.toBaseIO
      results.modify fun found => found.setIfInBounds index (some result)
  let workers ← (Array.range (max width 1)).mapM fun _ =>
    IO.asTask (prio := .dedicated) worker
  for task in workers do
    discard <| IO.wait task
  results.get

/-- Compile one planted module with `lean`, as Lake compiles a module of the
package: the loader's search path and the package's `-D` options. -/
def compile (run : Run) (job : CompileJob) : IO CompileResult := do
  let started ← IO.monoMsNow
  let source := job.source
  if let some parent := source.parent then IO.FS.createDirAll parent
  IO.FS.writeFile source job.text
  let output ← IO.Process.output
    { cmd := run.leanExecutable.toString
      args := #["-R", job.directory.toString] ++ run.leanOptions ++
        #["-o", job.olean.toString, source.toString]
      env := #[("LEAN_PATH", some run.leanPath)] }
  return { exitCode := output.exitCode, output := output.stdout ++ output.stderr,
           milliseconds := (← IO.monoMsNow) - started }

/-! ## The in-tree command over a planted root -/

/-- The directories the in-tree command reads as audited sources. -/
def auditedDirectories : List String :=
  ["Whatwg", "WhatwgTest", "WhatwgGates", "whatwgbin"]

/-- The three roots beside them. -/
def auditedRoots : List String :=
  ["Whatwg.lean", "WhatwgGates.lean", "WhatwgTest.lean"]

/-- Elaborate a row's planted root with `lean`, so that the in-tree command
judges the planted tree with no build of it. The audited sources are copied to a
directory of their own, about five megabytes, with the row's texts in place: the
command finds its project root from the file it runs in and reads the sources
below it. The built tree is read through the loader's search path, and each
compiled plant's built file is given by path in a module setup file, as Lake
gives `lean` the files of a module's imports. -/
def elaborateRoot (run : Run) (overlay : Overlay) (compiled : Array (Name × System.FilePath)) :
    IO CompileResult := do
  let started ← IO.monoMsNow
  let directory ← run.newDirectory "intree"
  for tree in auditedDirectories do
    copyTree (run.root / tree) (directory / tree)
  for file in auditedRoots do
    IO.FS.writeBinFile (directory / file) (← IO.FS.readBinFile (run.root / file))
  for (path, planted) in overlay.entries do
    let target := directory / (← relativeTo run.root path)
    match planted with
    | some text =>
        if let some parent := target.parent then IO.FS.createDirAll parent
        IO.FS.writeFile target text
    | none =>
        if ← target.pathExists then IO.FS.removeFile target
  let arts : NameMap ImportArtifacts := compiled.foldl (init := {}) fun arts (moduleName, olean) =>
    arts.insert moduleName (.ofArrays #[#[olean]])
  let setup : ModuleSetup := { name := `WhatwgTest, importArts := arts }
  let setupFile := directory / "WhatwgTest.setup.json"
  IO.FS.writeFile setupFile (toJson setup).compress
  let output ← IO.Process.output
    { cmd := run.leanExecutable.toString
      args := #["--setup", setupFile.toString] ++ run.leanOptions ++
        #[(directory / "WhatwgTest.lean").toString]
      env := #[("LEAN_PATH", some run.leanPath)] }
  return { exitCode := output.exitCode, output := output.stdout ++ output.stderr,
           milliseconds := (← IO.monoMsNow) - started }

/-- The class of an in-tree twin's line. -/
def inTreeClassName : String :=
  "real build: the in-tree command over the planted root"

/-- The in-tree twin of a row: the command must refuse the planted root and
print every fragment that it alone prints. -/
def judgeInTree (row : Row) (result : Option (Except IO.Error CompileResult)) : Outcome :=
  let fail (reason : String) (detail : Array String := #[]) : Outcome :=
    { label := row.label, ok := false, className := inTreeClassName,
      err := #[s!"FAIL {reason}"] ++ detail.map fun line => s!"  {line}" }
  match result with
  | some (.ok ran) =>
      if ran.exitCode == 0 then
        fail s!"in-tree command unexpectedly accepted {row.label}"
      else
        let missing := row.inTreeOnly.filter fun fragment =>
          (ran.output.splitOn fragment).length ≤ 1
        if missing.isEmpty then
          { label := row.label, ok := true, className := inTreeClassName,
            milliseconds := ran.milliseconds,
            out := #[s!"PASS in-tree command refused {row.label} with every diagnostic only it prints: {row.inTreeOnly} [lean over the planted root]"] }
        else
          fail s!"in-tree command refused {row.label} without the diagnostic only it prints; missing: {missing}"
            (lastLines ran.output 60)
  | some (.error error) =>
      fail s!"could not elaborate the planted root of {row.label}: {error}"
  | none => fail s!"the planted root of {row.label} was not elaborated"

/-- What the runs of `lake` gave, one after another in one task: the executable
gate over the unmodified tree, the package of each build-option row with its
control, and the narrow runs. -/
structure LakeResults where
  executable : UInt32 × String
  /-- The control package, with no plant, when a build-option row is judged. -/
  controlPackage? : Option (Except IO.Error PackageResult) := none
  packages : Array (String × Except IO.Error PackageResult) := #[]
  narrow : Array (NarrowRun × UInt32 × String × Nat) := #[]
  milliseconds : Nat := 0

def runLake (run : Run) (packageRows : Array (Row × String)) (narrowSelected : Array NarrowRun) :
    IO LakeResults := do
  let started ← IO.monoMsNow
  let gate ← IO.Process.output
    { cmd := lakeCommand, args := #["exe", executableGate], cwd := some run.root }
  let mut results : LakeResults := { executable := (gate.exitCode, gate.stdout ++ gate.stderr) }
  unless packageRows.isEmpty do
    let control ← (do buildPackage run (← IO.FS.readFile (lakefileSource run.root))).toBaseIO
    results := { results with controlPackage? := some control }
    for (row, lakefileText) in packageRows do
      let built ← (buildPackage run lakefileText).toBaseIO
      results := { results with packages := results.packages.push (row.label, built) }
  for narrow in narrowSelected do
    let narrowStarted ← IO.monoMsNow
    let output ← IO.Process.output
      { cmd := lakeCommand, args := #["env", "lean", narrow.file], cwd := some run.root }
    results := { results with
      narrow := results.narrow.push
        (narrow, output.exitCode, output.stdout ++ output.stderr,
          (← IO.monoMsNow) - narrowStarted) }
  return { results with milliseconds := (← IO.monoMsNow) - started }

/-- A narrow run, judged as the one-plant run judges it. -/
def judgeNarrow (narrow : NarrowRun) (exitCode : UInt32) (text : String) : Outcome :=
  let className := "real build: the command itself"
  if exitCode != 0 then
    { label := narrow.label, ok := false, className,
      err := #[s!"FAIL {narrow.label}: `lake env lean {narrow.file}` exited with code {exitCode}"] ++
        (errorLines text).toArray.map fun line => s!"  {line}" }
  else
    let missing := narrow.templates.filter fun template => !(templateMatches template text)
    if missing.isEmpty then
      { label := narrow.label, ok := true, className,
        out := #[s!"PASS {narrow.label}: exit code 0 and a line matching each of {narrow.templates}"] }
    else
      { label := narrow.label, ok := false, className,
        err := #[s!"FAIL {narrow.label}: exit code 0, but no line matches:"] ++
          missing.toArray.map (s!"  {·}") ++ lastLines text 60 }

/-! ## The run -/

/-- Print a note on standard error with the time since `started`. -/
def note (started : Nat) (text : String) : IO Unit := do
  let tenths := ((← IO.monoMsNow) - started) / 100
  IO.eprintln s!"NOTE [{tenths / 10}.{tenths % 10} s] {text}"

/-- Print a row's lines. -/
def Outcome.print (outcome : Outcome) : IO Unit := do
  for line in outcome.out do IO.println line
  (← IO.getStdout).flush
  for line in outcome.err do IO.eprintln line

/-- The in-process run over the checkout at `root`: the controls, every selected
row, and the narrow runs. `width` is how many `lean` processes compile plants at
a time. -/
def runInProcess (base : Trust.Config) (root scratch : System.FilePath) (selection : Selection)
    (width : Nat) : IO Bool := do
  let started ← IO.monoMsNow
  let mut allOk := true
  -- The declared red set. A red module has no built file, and this run builds none.
  let declared ← knownRed root
  unless declared.isEmpty do
    IO.eprintln s!"FAIL {declared.length} module(s) are declared red in test/fixtures/trust-gate/known-red.txt; the in-process run needs every module built, so judge this tree with --each"
    return false
  IO.println "PASS declared red set is empty"
  -- Steps 0 to 2 of the executable over the tree as it stands: the run reads its
  -- built files, so they must be the sources'.
  let moduleNames ← Trust.moduleSources base root
  let unbuilt := (← Trust.buildConfigurationFindings root) ++
    (← Trust.freshnessFindings root moduleNames)
  let unbuilt ← if unbuilt.isEmpty then Trust.optionFindings root moduleNames else pure unbuilt
  unless unbuilt.isEmpty do
    IO.eprintln "FAIL the tree is not built and fresh; run `lake build` first. The executable gate's steps 0 to 2 find:"
    for finding in unbuilt do IO.eprintln s!"  {finding}"
    return false
  IO.println s!"PASS the built tree is the sources': steps 0 to 2 of the executable gate have no finding over {moduleNames.size} module sources"
  -- Plan every selected row: its planted texts and the modules lean compiles.
  let counter ← IO.mkRef 0
  let sysroot ← Lean.findSysroot
  let searchPath ← Trust.loaderSearchPath root sysroot
  let (_, recorded) ← Trust.traceOf (Trust.leanBuildDir root) root `Whatwg
  let mut planned : Array (Except String Planned) := #[]
  let mut jobs : Array CompileJob := #[]
  let mut replacedModules : NameSet := {}
  for row in plantedRows do
    unless selection.includes row.label do continue
    let plan : IO Planned := do
      let overlay ← plantEdits root (row.edits ++ row.afterBuild)
      return { row, overlay }
    match ← plan.toBaseIO with
    | .error error => planned := planned.push (.error s!"could not plant {row.label}: {error}")
    | .ok plan =>
        let mut indices : Array Nat := #[]
        let mut inTreeIndices : Array Nat := #[]
        let judgedOnPlant := row.judgement == .compiled || row.judgement == .leanRefuses
        let hasTwin := !row.inTreeOnly.isEmpty
        if judgedOnPlant || hasTwin then
          for (moduleName, text) in ← plantedModules root plan.overlay do
            let index ←
              match jobs.findIdx? fun job => job.moduleName == moduleName && job.text == text with
              | some index => pure index
              | none =>
                  let index := jobs.size
                  jobs := jobs.push
                    { moduleName, text, directory := scratch / s!"compile-{index}" }
                  pure index
            if judgedOnPlant then indices := indices.push index
            if hasTwin then inTreeIndices := inTreeIndices.push index
            if row.judgement == .compiled &&
                (← (Lean.modToFilePath root moduleName "lean").pathExists) then
              replacedModules := replacedModules.insert moduleName
        planned := planned.push (.ok { plan with jobs := indices, inTreeJobs := inTreeIndices })
  -- The import graph of the audited modules, for the modules a plant replaces.
  let sources ← Trust.auditedSources root
  let mut importsOf : Array (Name × Array Name) := #[]
  for source in sources.modules do
    let moduleName := (← moduleNameOf root source).toName
    match ← Trust.headerImports source with
    | .ok imports => importsOf := importsOf.push (moduleName, imports)
    | .error reason =>
        throw <| IO.userError s!"the header of {source} does not parse: {reason}"
  let replaced := importersOf importsOf replacedModules
  let rootFile := testRoot root
  let rootImports ← headerImportsOfText (← IO.FS.readFile rootFile) "WhatwgTest.lean"
  note started s!"planned {planned.size} row(s) and {jobs.size} compile(s); {replacedModules.size} module(s) are replaced by a plant and {replaced.size} import or are one"
  -- Start the processes beside the judging: the compiles, and one task for lake.
  let leanExecutable := (sysroot / "bin" / "lean").addExtension System.FilePath.exeExtension
  let leanPath := System.SearchPath.toString (searchPath.filter (· != sysroot / "lib" / "lean"))
  -- One import of the built tree, in two stages, with no extension loaded.
  Trust.initLoaderSearchPath root
  let earlyImports := rootImports.filter fun entry => !replaced.contains entry.module
  let (earlyState, baseState, environment) ← withImporting do
    let (_, earlyState) ← (importModulesCore earlyImports).run
    let (_, baseState) ← (importModulesCore rootImports).run earlyState
    let environment ← finalizeImport baseState rootImports {} 0 (leakEnv := false) (loadExts := false)
    pure (earlyState, baseState, environment)
  note started s!"imported {environment.header.moduleNames.size} modules"
  let reads : Trust.HostReads :=
    { tokenTable := ← Trust.rebuiltTokenTable environment
      scopedTokens := Trust.rawScopedTokens environment
      rootConstants := #[] }
  let mut run : Run :=
    { root, scratch, counter, base, sources, replaced, earlyState, baseState,
      environment, reads, tokens := sortedTokens reads.tokenTable, scans := {}, memo := {},
      memoWithoutReplaced := {}, leanExecutable, leanPath, leanOptions := recorded }
  let compileTask ← IO.asTask (prio := .dedicated)
    (runPool width (jobs.map fun job => compile run job))
  -- The in-tree twins: each planted root elaborated by lean, once its plants are
  -- compiled, beside the judging of the compiled rows.
  let twins := planned.filterMap fun plan =>
    match plan with
    | .ok plan => if plan.row.inTreeOnly.isEmpty then none else some plan
    | .error _ => none
  let twinTask ← IO.asTask (prio := .dedicated) do
    let compiled : Array (Option (Except IO.Error CompileResult)) ←
      match ← IO.wait compileTask with
      | .ok compiled => pure compiled
      | .error error => throw error
    runPool width <| twins.map fun plan => do
      let mut plants : Array (Name × System.FilePath) := #[]
      for index in plan.inTreeJobs do
        let job? : Option CompileJob := jobs[index]?
        let result? : Option (Except IO.Error CompileResult) := compiled[index]?.join
        match job?, result? with
        | some job, some (.ok result) =>
            if result.exitCode != 0 then
              throw <| IO.userError
                s!"lean did not accept module {job.moduleName}: {lastLines result.output 8}"
            plants := plants.push (job.moduleName, job.olean)
        | _, _ => throw <| IO.userError s!"compile job {index} gave no result"
      elaborateRoot run plan.overlay plants
  let packageRows ← (planned.filterMap fun plan =>
      match plan with
      | .ok plan => if plan.row.judgement == .lakeOptions then some plan else none
      | .error _ => none).filterMapM fun plan => do
    match plan.overlay.find? (lakefileSource root) with
    | some (some text) => return some (plan.row, text)
    | _ => return none
  let narrowSelected := narrowRuns.toArray.filter fun narrow => selection.includes narrow.label
  let lakeTask ← IO.asTask (prio := .dedicated) (runLake run packageRows narrowSelected)
  -- Scan every source on disk once, and traverse every audited declaration once.
  let mut scans : Std.HashMap String Trust.SourceScan := {}
  for source in sources.modules ++ sources.entryPoints do
    scans := scans.insert (Trust.pathKey source)
      (← Trust.scanSource environment reads.tokenTable source)
  let mut memo : Std.HashMap Name (Array Name) := {}
  match Trust.auditedDeclarations base environment with
  | .ok declarations =>
      for declaration in declarations do
        memo := (Trust.traverseAxioms environment Trust.axiomTraversalFuel memo declaration.name).memo
  | .error message => throw <| IO.userError message
  let mut memoWithoutReplaced := memo
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if replaced.contains moduleName then
      for name in Trust.moduleDeclarations environment index do
        memoWithoutReplaced := memoWithoutReplaced.erase name
  run := { run with scans, memo, memoWithoutReplaced }
  note started s!"scanned {scans.size} sources and closed {memo.size} constants"
  -- The control: the gate's run over the unplanted view.
  let (controlFindings, controlSummary?) ← gateFindings run base {} environment false false
  let controlSummary ←
    match controlFindings.isEmpty, controlSummary? with
    | true, some summary =>
        IO.println "PASS in-process gate run accepted the unmodified source tree"
        pure summary.line
    | _, _ =>
        IO.eprintln "FAIL the in-process gate run rejected the unmodified source tree"
        for finding in controlFindings do IO.eprintln s!"  {finding}"
        return false
  (← IO.getStdout).flush
  -- Rows the built environment judges, while the compiles run.
  let mut outcomes : Std.HashMap String Outcome := {}
  for plan in planned do
    match plan with
    | .error message =>
        allOk := false
        IO.eprintln s!"FAIL {message}"
    | .ok plan =>
        let rowStarted ← IO.monoMsNow
        let judged : Option (IO Outcome) :=
          match plan.row.judgement with
          | .passes => some (judgeByRun run plan jobs #[])
          | .freshness => some (judgeFreshness run plan)
          | _ => none
        if let some judge := judged then
          let outcome ← match ← judge.toBaseIO with
            | .ok outcome => pure outcome
            | .error error => pure (failed root plan.row s!"could not judge {plan.row.label}: {error}")
          outcomes := outcomes.insert plan.row.label
            { outcome with milliseconds := (← IO.monoMsNow) - rowStarted }
  note started s!"judged {outcomes.size} row(s) on the built environment"
  -- Rows that wait for lean.
  let results ← match ← IO.wait compileTask with
    | .ok results => pure results
    | .error error => throw error
  let mut compileMilliseconds := 0
  for result in results do
    if let some (.ok result) := result then
      compileMilliseconds := compileMilliseconds + result.milliseconds
  note started s!"lean compiled {jobs.size} plant(s), {compileMilliseconds / 1000} s of process time"
  for plan in planned do
    let .ok plan := plan | continue
    let rowStarted ← IO.monoMsNow
    let judged : Option (IO Outcome) :=
      match plan.row.judgement with
      | .compiled => some (judgeByRun run plan jobs results)
      | .leanRefuses => some (judgeLeanRefusal run plan jobs results)
      | _ => none
    if let some judge := judged then
      let outcome ← match ← judge.toBaseIO with
        | .ok outcome => pure outcome
        | .error error => pure (failed root plan.row s!"could not judge {plan.row.label}: {error}")
      outcomes := outcomes.insert plan.row.label
        { outcome with milliseconds := (← IO.monoMsNow) - rowStarted }
  note started s!"judged the compiled rows"
  -- What lake gave.
  let lake ← match ← IO.wait lakeTask with
    | .ok lake => pure lake
    | .error error => throw error
  note started s!"lake ran for {lake.milliseconds / 1000} s beside the judging"
  -- The executable accepts the same tree with the same counts.
  let twin ← do
    let (exitCode, text) := lake.executable
    match readExecutableVerdict exitCode text with
    | .accepted verdictLine =>
        if summaryOf? verdictLine == summaryOf? controlSummary then
          IO.println "PASS executable gate accepted the unmodified source tree with the in-process run's counts"
          pure true
        else
          IO.eprintln s!"FAIL executable gate accepted the unmodified source tree, but its summary differs from the in-process run's: executable [{verdictLine}], in process [{controlSummary}]"
          pure false
    | .refused =>
        IO.eprintln "FAIL executable gate unexpectedly refused the unmodified source tree"
        for line in lastLines text 60 do IO.eprintln line
        pure false
    | .couldNotRun =>
        IO.eprintln s!"FAIL could not run the executable gate for the unmodified source tree: `lake exe {executableGate}` exited with code {exitCode} and printed no verdict line"
        for line in lastLines text do IO.eprintln line
        pure false
  allOk := allOk && twin
  -- The control of the one-module package, then its rows.
  if let some control := lake.controlPackage? then
    let ok ← match control with
      | .ok built =>
          if built.exitCode == 0 && built.freshness.isEmpty && built.options.isEmpty then
            IO.println "PASS the one-module package with no plant builds, and the freshness and recorded-options steps have no finding over it"
            pure true
          else
            IO.eprintln s!"FAIL the one-module package with no plant: lake exit code {built.exitCode}"
            for line in built.freshness ++ built.options ++ lastLines built.output do
              IO.eprintln s!"  {line}"
            pure false
      | .error error =>
          IO.eprintln s!"FAIL could not build the one-module package with no plant: {error}"
          pure false
    allOk := allOk && ok
  for plan in planned do
    let .ok plan := plan | continue
    unless plan.row.judgement == .lakeOptions do continue
    let outcome :=
      match lake.packages.find? fun (label, _) => label == plan.row.label with
      | some (_, built) =>
          let judged := judgePackage root plan.row built
          { judged with milliseconds := match built with
              | .ok built => built.milliseconds
              | .error _ => 0 }
      | none => failed root plan.row s!"{plan.row.label} plants no lakefile.toml to build"
    outcomes := outcomes.insert plan.row.label outcome
  -- What the in-tree command said of the planted roots.
  let twinResults ← match ← IO.wait twinTask with
    | .ok twinResults => pure twinResults
    | .error error => throw error
  let mut twinOutcomes : Std.HashMap String Outcome := {}
  for index in [0:twins.size] do
    let some plan := twins[index]? | continue
    twinOutcomes := twinOutcomes.insert plan.row.label (judgeInTree plan.row twinResults[index]?.join)
  note started s!"lean elaborated {twins.size} planted root(s) for the in-tree command"
  (← IO.getStdout).flush
  -- Every row's lines, in the order of the one-plant run.
  let mut classMilliseconds : Std.HashMap String (Nat × Nat) := {}
  for row in plantedRows do
    unless selection.includes row.label do continue
    for outcome in (outcomes[row.label]?).toList ++ (twinOutcomes[row.label]?).toList do
      -- A row that could not be planted has no outcome, and has printed its line.
      outcome.print
      allOk := allOk && outcome.ok
      let (count, total) := classMilliseconds.getD outcome.className (0, 0)
      classMilliseconds := classMilliseconds.insert outcome.className
        (count + 1, total + outcome.milliseconds)
  for (narrow, exitCode, text, milliseconds) in lake.narrow do
    let outcome := judgeNarrow narrow exitCode text
    outcome.print
    allOk := allOk && outcome.ok
    let (count, total) := classMilliseconds.getD outcome.className (0, 0)
    classMilliseconds := classMilliseconds.insert outcome.className (count + 1, total + milliseconds)
    -- The in-tree command prints the summary the in-process run computed.
    if narrow.templates.contains gateSummaryTemplate && outcome.ok then
      if summaryOf? text == summaryOf? controlSummary then
        IO.println "PASS the in-tree command's summary of the unmodified source tree equals the in-process run's"
      else
        allOk := false
        IO.eprintln s!"FAIL the in-tree command's summary differs from the in-process run's: in process [{controlSummary}]"
  (← IO.getStdout).flush
  let byClass := (classMilliseconds.toArray.qsort fun left right => left.1 < right.1).map
    fun (name, count, total) => s!"{name}: {count} row(s), {total} ms"
  IO.eprintln s!"NOTE judging time by class, compiles and lake apart: {"; ".intercalate byClass.toList}"
  note started s!"done"
  return allOk

/-! ## Command line -/

def usage : String :=
  "usage: lake exe whatwg_trustselftest [--each] [--rows <label-prefix>]... [--jobs <n>]"

/-- What the arguments ask for. -/
structure Arguments where
  each : Bool := false
  labelPrefixes : List String := []
  jobs : Nat := 4

/-- Read the arguments; `none` for one that is not understood. -/
def parseArguments : List String → Arguments → Option Arguments
  | [], found => some found
  | "--each" :: rest, found => parseArguments rest { found with each := true }
  | "--rows" :: labelPrefix :: rest, found =>
      parseArguments rest { found with labelPrefixes := found.labelPrefixes ++ [labelPrefix] }
  | "--jobs" :: count :: rest, found =>
      match count.toNat? with
      | some width => if width == 0 then none else parseArguments rest { found with jobs := width }
      | none => none
  | _, _ => none

/-- Command-line entry, invoked by `whatwgbin/TrustSelfTest.lean` with this
repository's configuration. With no flag every row is judged in process; with
`--each` the one-plant run of `WhatwgGates/TrustSelfTest.lean` is made. -/
def cli (base : Trust.Config) (args : List String) : IO UInt32 := do
  let some arguments := parseArguments args {}
    | IO.eprintln usage
      return 2
  let selection : Selection := { labelPrefixes := arguments.labelPrefixes }
  for labelPrefix in arguments.labelPrefixes do
    unless rowLabels.any (·.startsWith labelPrefix) do
      IO.eprintln s!"no row label begins with `{labelPrefix}`"
      IO.eprintln usage
      return 2
  let root ← Gates.Common.projectRoot
  if arguments.each then
    return ← runEach root selection
  let scratchBase : System.FilePath ←
    match ← IO.getEnv "TMPDIR" with
    | some directory => pure directory
    | none =>
      match ← IO.getEnv "TEMP" with
      | some directory => pure directory
      | none => pure "/tmp"
  let scratch := scratchBase / s!"whatwg-trust-inprocess-{← IO.monoNanosNow}"
  IO.FS.createDirAll scratch
  let started ← IO.monoMsNow
  let ok ← try
      runInProcess base root scratch selection arguments.jobs
    finally
      IO.FS.removeDirAll scratch
  let seconds := ((← IO.monoMsNow) - started) / 1000
  if ok then
    let scope :=
      if selection.labelPrefixes.isEmpty then ""
      else s!" (only the rows whose label begins with one of {selection.labelPrefixes})"
    IO.println s!"PASS trust self-test, in process{scope}: the gate library's run rejected every planted declaration for its stated reason, every control was accepted, and every narrow run exited 0 with its frozen summary; {seconds} s"
    return 0
  IO.eprintln s!"FAIL trust self-test, in process; judge a failing row alone with `lake exe whatwg_trustselftest --each --rows <its label>`; {seconds} s"
  return 1

end Gates.TrustSelfTest.InProcess
