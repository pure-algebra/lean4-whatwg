import Lake.Toml.Load
import WhatwgGates.Trust.Gate
import WhatwgGates.Trust.Load

/-!
# Gates.Trust.Main

The executable trust gate, `lake exe whatwg_trustgate` (addendum V2e.5 of
`test/contracts/trust-gate-hardening.contract.md`, rulings R-W7(a), R-W14(b) and
R-W15(a)). The entry point `whatwgbin/TrustGate.lean` hands this repository's
`Gates.TrustConfig.config` to `cli`; everything else is here.

## Why an executable

The in-tree command `#whatwg_streams_axiom_gate` runs inside the elaboration of
the tree it audits, so audited code that runs first can replace it or remove its
post-command check (debt D56; plant V2e-G1 builds green under `lake build`).
This gate runs in its own process over the built `.olean` files. It imports them
through `WhatwgGates/Trust/Load.lean` with no environment extension loaded, so no
audited initializer, parser descriptor, macro or elaborator runs here; it never
calls `Lean.enableInitializersExecution`, `Lean.Environment.evalConst` or any
evaluation of an imported constant, and declares nothing `unsafe` or `partial`.
The only audited code linked into it is the gate library, the loader, this
module and the config module (step 6 checks the last part).

## Steps, in order

0. *Build configuration*, read from the project root: `lakefile.toml` sets no
   `weakLeanArgs`, which Lake keeps out of every trace, read lexically (the word
   outside a `#` comment, unless that line sets it to `[]`) and, as a backstop,
   through Lake's own TOML reader over every table, so that an escaped key or an
   inline table whose string holds a `#` cannot hide one; and no
   `lakefile.lean` exists, which Lake would read in its place.
1. *Freshness*, over every module source (each `.lean` file of the audited
   trees, the root `WhatwgTest.lean` excepted): its built `.olean` exists, and
   its Lake trace is fresh by the loader's `traceOf` (it parses, names the
   module and records the source's hash today). A trace that does not also
   record, among its outputs, the hash of the `.olean` beside it is stale too:
   the built file is then not the one that build wrote.
2. *Recorded options*, over every module source's trace: `-DwarningAsError=true`
   is recorded; no recorded option sets `warningAsError` to anything else, names
   `warn.sorry` or begins `debug.` (names compared with guillemets removed);
   every `Module.leanArgs` argument is `-D<name>=<value>`; every `libs` entry
   carries Lake's empty hash.
3. *Import* of the import set, the modules the root's header imports, read with
   Lean's own header parser. The root itself is never imported.
4. *The in-tree passes*, `Gates.Trust.runPasses`, with this host's reads: the
   final token table rebuilt from `Lean.Parser.builtinTokenTable` and every
   module's raw global `.token` parser entries, then `updateTokens`; every raw
   scoped `.token` entry; no root constants; and the axioms of each constant by
   this module's own traversal of the kernel declarations, bounded by fuel
   (below).
5. *Extension allowlist*: every extension holding an entry of an audited module
   is on `Config.extensionAllowlist`, and every entry of that list names one
   that does, carries a reason and occurs once.
6. *Link closure*: the import closure of the entry point holds no listed
   metaprogramming module, whose initializers would run in this process.
7. *Verdict*: `PASS whatwg_trustgate: ` and the summary line, exit code 0; or
   `FAIL whatwg_trustgate: <n> finding(s)`, exit code 1. A finding of step 1 or
   step 3 stops the run before the next step, since what follows would read an
   environment that is not the sources'. A usage error or an internal failure
   exits with code 2 and prints no verdict.

Every finding is one line `FAIL <message>` on standard output, the message the
contract freezes for its step (the in-tree passes' messages are the library's,
letter for letter); the verdict is the last line of standard output. A note of
the time each step took goes to standard error.

## The axiom traversal

`Lean.collectAxioms` reads, for every imported constant, the table the
constant's own module wrote when it was elaborated (`exportedAxiomsExt`). This
gate reads no such table: `traverseAxioms` walks each constant's kernel type and
value with the algorithm of `Lean.CollectAxioms.collect`, over the constants the
kernel declarations mention, every audited declaration first and in the order
those tables were written (module by module, each module's constants in its own
order), with one memo for the run. Its answers equal `Lean.collectAxioms` over
the loaded environment for every audited declaration of the unmodified tree,
measured. They are not the exact transitive closure: `collect` records a
constant with no axioms while it is on its stack, so around a dependency cycle
(an inductive type and its constructors, a compiled recursive function) a member
can miss an axiom only another member reaches. Such a cycle never leaves one
module, and every member of an audited module is audited, so an axiom any member
reaches is reported on the member that reaches it directly. The walk is an
explicit stack bounded by `axiomTraversalFuel` steps per root; exhausting it is
a finding, never a silent answer.

## What it does not see

Sections 13, V2b.6, V2c.7 and V2e.7 of the contract. In particular: the source
passes are lexical and the same code as the in-tree command's; a declaration
added with the kernel check off stays with `leanchecker`; the toolchain, Lake and
its trace hashing, and a trace and a built file forged together are trusted; the
root's own constants are not read, since the root is never imported.
-/

namespace Gates.Trust

open Lean

/-! ## Small string helpers -/

/-- A string with leading and trailing whitespace removed. -/
def strip (text : String) : String :=
  String.ofList ((text.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- A string with every whitespace character removed. -/
def withoutWhitespace (text : String) : String :=
  String.ofList (text.toList.filter (!·.isWhitespace))

/-- The text before the first occurrence of `separator`, and the text after it. -/
def splitFirst (text separator : String) : Option (String × String) :=
  match text.splitOn separator with
  | first :: rest@(_ :: _) => some (first, separator.intercalate rest)
  | _ => none

/-! ## Step 0: the build configuration -/

/-- The key Lake keeps out of every trace. -/
def weakLeanArgsKey : String := "weakLeanArgs"

/-- The text of a `lakefile.toml` line before its first `#`. -/
def beforeTomlComment (line : String) : String :=
  (line.splitOn "#").headD ""

/-- Whether a line, its comment removed, sets `weakLeanArgs` to the empty array. -/
def setsEmptyWeakLeanArgs (code : String) : Bool :=
  match splitFirst code "=" with
  | some (key, value) => strip key == weakLeanArgsKey && withoutWhitespace value == "[]"
  | none => false

/-- The lexical rule of step 0: every line of `lakefile.toml` whose text before
its first `#` holds the word `weakLeanArgs`, unless that line sets it to `[]`. -/
def lexicalWeakLeanArgsFindings (text : String) : Array String := Id.run do
  let mut findings : Array String := #[]
  let mut lineNumber := 0
  for line in text.splitOn "\n" do
    lineNumber := lineNumber + 1
    let code := beforeTomlComment line
    if (code.splitOn weakLeanArgsKey).length > 1 && !setsEmptyWeakLeanArgs code then
      findings := findings.push
        s!"Whatwg trust gate: lakefile.toml sets weakLeanArgs, which Lake keeps out of every trace: line {lineNumber}"
  return findings

/-- Values one TOML walk may visit. A lakefile has a few hundred. -/
def tomlWalkFuel : Nat := 1000000

/-- Every key path of a TOML table whose last key is `weakLeanArgs` and whose
value is not the empty array, read through Lake's own TOML reader, at any depth:
the package table, every `lean_lib` and `lean_exe` table, and every inline table
or array. -/
def tomlWeakLeanArgsPaths (table : Lake.Toml.Table) : Except String (Array String) := Id.run do
  -- Each pending value with its path and, when a table holds it directly, its key.
  let mut pending : Array (String × Option Name × Lake.Toml.Value) :=
    table.items.map fun (key, value) => (toString key, some key, value)
  let mut found : Array String := #[]
  for _ in [0:tomlWalkFuel] do
    match pending.back? with
    | none => return .ok found
    | some (path, key?, value) =>
        pending := pending.pop
        let isWeakLeanArgs := match key? with
          | some (.str _ last) => last == weakLeanArgsKey
          | _ => false
        if isWeakLeanArgs then
          match value with
          | .array _ items => unless items.isEmpty do found := found.push path
          | _ => found := found.push path
        match value with
        | .table' _ inner =>
            for (key, item) in inner.items do
              pending := pending.push (s!"{path}.{key}", some key, item)
        | .array _ items =>
            for item in items do
              pending := pending.push (s!"{path}[]", none, item)
        | _ => pure ()
  return .error s!"the walk over lakefile.toml exceeded {tomlWalkFuel} values"

/-- The structural backstop of step 0: `lakefile.toml` read by Lake's TOML
reader, and every non-empty `weakLeanArgs` it sets anywhere. -/
def tomlWeakLeanArgsFindings (text : String) : IO (Array String) := do
  let context := Parser.mkInputContext text "lakefile.toml"
  match ← (Lake.Toml.loadToml context).toBaseIO with
  | .error log =>
      let first ← match log.toList.head? with
        | some message => message.data.toString
        | none => pure "no message"
      return #[s!"Whatwg trust gate: lakefile.toml does not parse as TOML, so the weakLeanArgs Lake would read cannot be judged: {first}"]
  | .ok table =>
      match tomlWeakLeanArgsPaths table with
      | .error reason =>
          return #[s!"Whatwg trust gate: lakefile.toml sets weakLeanArgs, which Lake keeps out of every trace: {reason}"]
      | .ok paths =>
          return paths.map fun path =>
            s!"Whatwg trust gate: lakefile.toml sets weakLeanArgs, which Lake keeps out of every trace: Lake's TOML reader finds it at {path}"

/-- Step 0 (addendum V2e.5). -/
def buildConfigurationFindings (projectRoot : System.FilePath) : IO (Array String) := do
  let mut findings : Array String := #[]
  let lakefile := projectRoot / "lakefile.toml"
  let text ← IO.FS.readFile lakefile
  let lexical := lexicalWeakLeanArgsFindings text
  findings := findings ++ lexical
  -- The backstop reports only what the lexical rule missed, so that one setting
  -- is one finding.
  let structural ← tomlWeakLeanArgsFindings text
  if lexical.isEmpty then
    findings := findings ++ structural
  if ← (projectRoot / "lakefile.lean").pathExists then
    findings := findings.push
      "Whatwg trust gate: lakefile.lean exists, and Lake reads it in place of lakefile.toml"
  return findings

/-! ## Steps 1 and 2: freshness and recorded options -/

/-- The test root, which runs the in-tree command and which this gate judges
lexically and never imports. -/
def rootModuleName : Name := `WhatwgTest

/-- The module sources: the module of every `.lean` file of the audited trees,
by the loader's enumeration, the root excepted. -/
def moduleSources (config : Config) (projectRoot : System.FilePath) : IO (Array Name) := do
  return (← sourceModules projectRoot config.auditedTrees).filter (· != rootModuleName)

/-- The hash a trace records for the built `.olean` among its outputs, if it
records exactly one such output: an entry `<hash>.olean` of `outputs.o`. -/
def recordedOleanHash? (traceText : String) : Option String := do
  let json ← (Json.parse traceText).toOption
  let outputs ← (json.getObjVal? "outputs").toOption
  let oleans ← (outputs.getObjVal? "o").toOption
  let items ← (oleans.getArr?).toOption
  let hashes := items.filterMap fun item =>
    match item.getStr? with
    | .ok name => (name.dropSuffix? ".olean").map (·.copy)
    | .error _ => none
  match hashes with
  | #[hash] => if hash.length == 16 then some hash else none
  | _ => none

/-- Why a module is stale, for the finding: the first of the trace's checks that
fails, in the loader's order, then the `.olean` hash. -/
def staleReason (buildRoot projectRoot : System.FilePath) (moduleName : Name) : IO String := do
  let tracePath := Lean.modToFilePath buildRoot moduleName "trace"
  match ← (IO.FS.readFile tracePath).toBaseIO with
  | .error _ => return "it has no readable trace"
  | .ok text =>
      match parseTrace text with
      | .error reason => return s!"its trace does not parse: {reason}"
      | .ok record =>
          if record.moduleName != moduleName then
            return s!"its trace names module {record.moduleName}"
          match ← (sourceHash (Lean.modToFilePath projectRoot moduleName "lean")).toBaseIO with
          | .error _ => return "its source cannot be read"
          | .ok hash =>
              if hash != record.sourceHash then
                return s!"its source has hash {hash} and its trace records {record.sourceHash}"
              return "its built .olean is not the one its trace records"

/-- Whether the `.olean` beside a fresh trace is the one the trace records. -/
def oleanMatchesTrace (buildRoot : System.FilePath) (moduleName : Name) : IO Bool := do
  match ← (IO.FS.readFile (Lean.modToFilePath buildRoot moduleName "trace")).toBaseIO with
  | .error _ => return false
  | .ok text =>
      match recordedOleanHash? text with
      | none => return false
      | some recorded =>
          match ← (Lake.computeBinFileHash (Lean.modToFilePath buildRoot moduleName "olean")).toBaseIO with
          | .ok hash => return hash.toString == recorded
          | .error _ => return false

/-- Step 1 (addendum V2e.5): every module source has a built `.olean` and a
fresh trace, and the trace records that `.olean`. -/
def freshnessFindings (projectRoot : System.FilePath) (modules : Array Name) :
    IO (Array String) := do
  let buildRoot := leanBuildDir projectRoot
  let mut findings : Array String := #[]
  for moduleName in modules do
    let hasOlean ← (Lean.modToFilePath buildRoot moduleName "olean").pathExists
    unless hasOlean do
      findings := findings.push s!"Whatwg trust gate: module {moduleName} has no built .olean"
    let (fresh, _) ← traceOf buildRoot projectRoot moduleName
    let recorded ← if fresh && hasOlean then oleanMatchesTrace buildRoot moduleName else pure true
    unless fresh && recorded do
      findings := findings.push
        s!"Whatwg trust gate: module {moduleName} is stale: {← staleReason buildRoot projectRoot moduleName}"
  return findings

/-- Lake's hash of nothing, which a trace records for an empty `libs` input. -/
def emptyLakeHash : String := "00000000000006bb"

/-- An option's name and value from its `-D<name>=<value>` spelling, the name
with guillemets removed, as the refusals compare it. -/
def recordedOptionParts? (option : String) : Option (String × String) := do
  let rest ← (option.dropPrefix? "-D").map (·.copy)
  let (name, value) ← splitFirst rest "="
  let name := String.ofList (name.toList.filter fun c => c != '«' && c != '»')
  return (strip name, value)

/-- Whether a recorded option is one step 2 refuses: `warningAsError` set to
anything but `true`, `warn.sorry`, or a name that begins `debug.`. An option
that does not read as `-D<name>=<value>` is refused too. -/
def isRefusedOption (option : String) : Bool :=
  match recordedOptionParts? option with
  | none => true
  | some (name, value) =>
      (name == "warningAsError" && value != "true") || name == "warn.sorry" ||
        name.startsWith "debug."

/-- Whether a `Module.leanArgs` argument has the form `-D<name>=<value>`. -/
def isDefineArgument (argument : String) : Bool :=
  match recordedOptionParts? argument with
  | some (name, value) => !name.isEmpty && !value.isEmpty
  | none => false

/-- Step 2 for one module (addendum V2e.5). -/
def recordedOptionFindings (moduleName : Name) (record : TraceRecord) : Array String := Id.run do
  let mut findings : Array String := #[]
  let options := record.recordedOptions
  unless options.contains "-DwarningAsError=true" do
    findings := findings.push
      s!"Whatwg trust gate: module {moduleName} was not compiled with -DwarningAsError=true"
  for option in options do
    if isRefusedOption option then
      findings := findings.push
        s!"Whatwg trust gate: module {moduleName} was compiled with the refused option {option}"
  for argument in record.leanArgs do
    unless isDefineArgument argument do
      findings := findings.push
        s!"Whatwg trust gate: module {moduleName} was compiled with the argument {argument}; only -D options are admitted"
  for (label, hash) in record.libs do
    unless hash == emptyLakeHash do
      findings := findings.push
        s!"Whatwg trust gate: module {moduleName} was compiled with a native library or plugin loaded into lean: {label} has hash {hash}"
  return findings

/-- Step 2 (addendum V2e.5), over every module source's trace. -/
def optionFindings (projectRoot : System.FilePath) (modules : Array Name) :
    IO (Array String) := do
  let buildRoot := leanBuildDir projectRoot
  let mut findings : Array String := #[]
  for moduleName in modules do
    let text ← IO.FS.readFile (Lean.modToFilePath buildRoot moduleName "trace")
    match parseTrace text with
    | .ok record => findings := findings ++ recordedOptionFindings moduleName record
    | .error reason =>
        findings := findings.push
          s!"Whatwg trust gate: module {moduleName} is stale: its trace does not parse: {reason}"
  return findings

/-! ## Step 3: the import set -/

/-- The modules a source's header imports, read with Lean's own header parser,
which stops at the first command; each module once, in order. The error is the
header's first error message. -/
def headerImports (file : System.FilePath) : IO (Except String (Array Name)) := do
  let text ← IO.FS.readFile file
  let (imports, _, messages) ← Elab.parseImports text (some file.toString)
  if messages.hasErrors then
    let first ← match messages.toList.head? with
      | some message => message.data.toString
      | none => pure "no message"
    return .error first
  let mut modules : Array Name := #[]
  for entry in imports do
    unless modules.contains entry.module do
      modules := modules.push entry.module
  return .ok modules

/-! ## Step 4: the host's reads -/

/-- The final token table, rebuilt as the parser extension's import builds it:
the `lean` binary's builtin table, every global `.token` entry of every imported
module's raw parser entries, then the module header's tokens. No parser is
evaluated and no extension is loaded. -/
def rebuiltTokenTable (environment : Environment) : IO Parser.TokenTable := do
  let mut table ← Parser.builtinTokenTable.get
  for index in [0:environment.header.moduleNames.size] do
    for entry in Parser.parserExtension.ext.getModuleEntries environment index do
      if let .global (.token token) := entry then
        if !token.isEmpty && (table.find? token).isNone then
          table := table.insert token token
  return Parser.Module.updateTokens table

/-- Every scoped `.token` entry of every imported module's raw parser entries:
the tokens token-table hygiene adds to the final table. -/
def rawScopedTokens (environment : Environment) : Array String := Id.run do
  let mut tokens : Array String := #[]
  for index in [0:environment.header.moduleNames.size] do
    for entry in Parser.parserExtension.ext.getModuleEntries environment index do
      if let .scoped _ (.token token) := entry then
        tokens := tokens.push token
  return tokens

/-- Steps one axiom traversal may take from one root. Each step opens a
constant, follows one dependency, or closes a constant, so a traversal takes at
most twice the constants plus the dependencies it meets. -/
def axiomTraversalFuel : Nat := 100000000

/-- The constants a constant's kernel declaration mentions, exactly the ones
`Lean.CollectAxioms.collect` follows at Lean 4.33.1: the type, the value of a
definition, theorem or `opaque`, and the constructors of an inductive type; a
recursor's rules are not followed. -/
def kernelDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray

/-- One open constant of the traversal: the dependencies it still has to follow
and the axioms found so far. -/
structure TraversalFrame where
  name : Name
  dependencies : Array Name
  next : Nat := 0
  found : NameSet

/-- The frame of a constant: its own name if it is an axiom, and its
dependencies; a name the environment does not hold has neither, as in
`Lean.CollectAxioms.collect`. -/
def openTraversalFrame (environment : Environment) (name : Name) : TraversalFrame :=
  match environment.find? name with
  | none => { name, dependencies := #[], found := {} }
  | some info =>
      { name, dependencies := kernelDependencies info,
        found := if info matches .axiomInfo _ then ({} : NameSet).insert name else {} }

/-- `found` with every axiom of `axioms` added. -/
def addAxioms (found : NameSet) (axioms : Array Name) : NameSet :=
  axioms.foldl (init := found) fun set axiomName => set.insert axiomName

/-- What one traversal returns: the root's axioms (sorted by `Name.lt`, as
`Lean.collectAxioms` returns them), or `none` when the fuel ran out; the memo
extended by every constant the traversal closed; the deepest stack and the
steps it took. -/
structure TraversalResult where
  axioms? : Option (Array Name)
  memo : Std.HashMap Name (Array Name)
  depth : Nat
  steps : Nat

/-- The axioms `root` reaches through the kernel declarations, by the algorithm
of `Lean.CollectAxioms.collect` at Lean 4.33.1 with an explicit stack in place
of its recursion: a constant entering the walk is recorded with no axioms until
it closes, a dependency already recorded contributes what is recorded for it,
and a closed constant's axioms join its parent's. Around a dependency cycle (an
inductive type and its constructors, a compiled recursive function) the answer
therefore depends on the order of the walk exactly as `collect`'s does. `memo`
holds every constant an earlier traversal closed and is extended with every
constant this one closes; a traversal that runs out of its `fuel` steps returns
no answer. -/
def traverseAxioms (environment : Environment) (fuel : Nat)
    (memo : Std.HashMap Name (Array Name)) (root : Name) : TraversalResult := Id.run do
  if let some known := memo[root]? then
    return { axioms? := some known, memo, depth := 0, steps := 0 }
  let mut memo := memo.insert root #[]
  let mut frames : Array TraversalFrame := #[openTraversalFrame environment root]
  let mut depth := 1
  let mut steps := 0
  for _ in [0:fuel] do
    steps := steps + 1
    let some top := frames.back? | break
    if h : top.next < top.dependencies.size then
      let dependency := top.dependencies[top.next]
      frames := frames.modify (frames.size - 1) fun frame => { frame with next := frame.next + 1 }
      match memo[dependency]? with
      | some known =>
          frames := frames.modify (frames.size - 1) fun frame =>
            { frame with found := addAxioms frame.found known }
      | none =>
          memo := memo.insert dependency #[]
          frames := frames.push (openTraversalFrame environment dependency)
          depth := max depth frames.size
    else
      let result := top.found.toArray.qsort Name.lt
      memo := memo.insert top.name result
      frames := frames.pop
      if frames.isEmpty then
        return { axioms? := some result, memo, depth, steps }
      frames := frames.modify (frames.size - 1) fun frame =>
        { frame with found := addAxioms frame.found result }
  return { axioms? := none, memo, depth, steps }

/-! ## Step 5: the extension allowlist -/

/-- Step 5 (addendum V2e.5): an audited module's entry in an extension the
allowlist does not name; then each list entry with a blank reason, listed more
than once, or naming an extension no audited module holds entries in. -/
def allowlistFindings (config : Config) (environment : Environment) : Array String := Id.run do
  let listed : Std.HashSet String :=
    config.extensionAllowlist.foldl (init := {}) fun set entry => set.insert entry.extension
  let mut findings : Array String := #[]
  let mut used : Std.HashSet String := {}
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if (treeOf? config moduleName).isNone then continue
    for (extension, _) in extensionsWithEntries environment index do
      let printed := toString extension
      used := used.insert printed
      unless listed.contains printed do
        findings := findings.push
          s!"Whatwg trust gate: module {moduleName} has entries in environment extension {printed}, which is not on the extension allowlist"
  let mut seen : Std.HashSet String := {}
  for entry in config.extensionAllowlist do
    if isBlank entry.reason then
      findings := findings.push
        s!"Whatwg trust gate: extension-allowlist entry for {entry.extension} carries no reason"
    if seen.contains entry.extension then
      findings := findings.push
        s!"Whatwg trust gate: extension-allowlist entry for {entry.extension} is listed more than once"
      continue
    seen := seen.insert entry.extension
    unless used.contains entry.extension do
      findings := findings.push
        s!"Whatwg trust gate: stale extension-allowlist entry for {entry.extension}; no audited module has entries in it"
  return findings

/-! ## Step 6: the link closure -/

/-- The executable's entry point, whose import closure step 6 reads. -/
def entryPointSource (projectRoot : System.FilePath) : System.FilePath :=
  projectRoot / "whatwgbin" / "TrustGate.lean"

/-- Modules one closure walk may visit. -/
def linkClosureFuel : Nat := 1000000

/-- Step 6 (addendum V2e.5): the import closure of the entry point's imports,
read with Lean's header parser and closed over the imported modules' headers,
holds no listed metaprogramming module. A module's header is read from the
imported environment when it holds the module (every audited module source is
fresh by step 1, so its header is its source's), else from its source when it
is under an audited tree, else from its built file. -/
def linkClosureFindings (config : Config) (environment : Environment)
    (projectRoot : System.FilePath) : IO (Array String) := do
  let entryPoint := entryPointSource projectRoot
  let start ← match ← headerImports entryPoint with
    | .ok modules => pure modules
    | .error reason =>
        throw <| IO.userError s!"the header of {entryPoint} does not parse: {reason}"
  let mut indexOf : Std.HashMap Name Nat := {}
  for index in [0:environment.header.moduleNames.size] do
    if let some moduleName := environment.header.moduleNames[index]? then
      indexOf := indexOf.insert moduleName index
  let listed := listedMetaprogrammingModules config
  let mut findings : Array String := #[]
  let mut visited : NameSet := {}
  let mut pending : Array Name := start
  for _ in [0:linkClosureFuel] do
    let some moduleName := pending.back? | return findings
    pending := pending.pop
    if visited.contains moduleName then continue
    visited := visited.insert moduleName
    if listed.contains moduleName then
      findings := findings.push
        s!"Whatwg trust gate: the executable's entry point whatwgbin/TrustGate.lean reaches the listed metaprogramming module {moduleName}"
    let imports ← match indexOf[moduleName]? with
      | some index =>
          pure ((environment.header.moduleData[index]?.map
            fun data => data.imports.map (·.module)).getD #[])
      | none =>
          let source := Lean.modToFilePath projectRoot moduleName "lean"
          if (treeOf? config moduleName).isSome && (← source.pathExists) then
            match ← headerImports source with
            | .ok modules => pure modules
            | .error reason =>
                throw <| IO.userError s!"the header of {source} does not parse: {reason}"
          else
            let (data, _) ← readModuleData (← findOLean moduleName)
            pure (data.imports.map (·.module))
    pending := pending ++ imports
  throw <| IO.userError s!"the link-closure walk exceeded {linkClosureFuel} modules"

/-! ## The run -/

/-- What the run has printed and measured. -/
structure RunState where
  findings : Nat := 0
  /-- Each step's or pass's label and milliseconds, in order. -/
  timings : Array (String × Nat) := #[]

/-- Print every finding as one `FAIL` line and count it. -/
def emitFindings (state : IO.Ref RunState) (findings : Array String) : IO Unit := do
  for finding in findings do
    IO.println s!"FAIL {finding}"
  state.modify fun current => { current with findings := current.findings + findings.size }

/-- Record how long a step took, ending now. -/
def recordTiming (state : IO.Ref RunState) (label : String) (started : Nat) : IO Nat := do
  let now ← IO.monoMsNow
  state.modify fun current => { current with timings := current.timings.push (label, now - started) }
  return now

/-- The pass labels of `runPasses`, in the order it reports them. -/
def passLabels : Array String :=
  #["root pass", "module closure", "modifier pass and token scan", "token-table hygiene",
    "environment pass and registrations", "axiom pass",
    "trust-token, keyword and configuration passes"]

/-- Print the verdict line and return the exit code. -/
def verdict (state : IO.Ref RunState) (summary? : Option Summary) : IO UInt32 := do
  let current ← state.get
  let timing := ", ".intercalate (current.timings.toList.map fun (label, ms) => s!"{label} {ms} ms")
  IO.eprintln s!"NOTE whatwg_trustgate timing: {timing}"
  if current.findings == 0 then
    match summary? with
    | some summary =>
        IO.println s!"PASS whatwg_trustgate: {summary.line}"
        return 0
    | none =>
        IO.eprintln "whatwg_trustgate: internal failure: no finding and no summary"
        return 2
  IO.println s!"FAIL whatwg_trustgate: {current.findings} finding(s)"
  return 1

/-- Every step of addendum V2e.5, in order, over the project that holds the
working directory. -/
def runGate (config : Config) : IO UInt32 := do
  let state ← IO.mkRef ({} : RunState)
  let started ← IO.monoMsNow
  let projectRoot ← findProjectRoot (← IO.currentDir)
  -- 0. The build configuration.
  emitFindings state (← buildConfigurationFindings projectRoot)
  -- 1. Freshness; a finding stops the run.
  let modules ← moduleSources config projectRoot
  let freshness ← freshnessFindings projectRoot modules
  emitFindings state freshness
  let mark ← recordTiming state "build configuration and freshness" started
  unless freshness.isEmpty do
    return ← verdict state none
  -- 2. Recorded options.
  emitFindings state (← optionFindings projectRoot modules)
  let mark ← recordTiming state "recorded options" mark
  -- 3. Import of the import set; a failure stops the run.
  let rootFile := projectRoot / "WhatwgTest.lean"
  let imported ← do
    match ← headerImports rootFile with
    | .error reason => pure (Except.error s!"the root's header does not parse: {reason}")
    | .ok importSet =>
        try
          initLoaderSearchPath projectRoot
          pure (.ok (← importBuilt importSet))
        catch error =>
          pure (.error (toString error))
  let environment ← match imported with
    | .ok environment => pure environment
    | .error reason =>
        emitFindings state #[s!"Whatwg trust gate: could not import the built environment: {reason}"]
        return ← verdict state none
  let mark ← recordTiming state "import" mark
  -- 4. The in-tree passes, with this host's reads.
  let reads : HostReads :=
    { tokenTable := ← rebuiltTokenTable environment
      scopedTokens := rawScopedTokens environment
      rootConstants := #[] }
  let memo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let exhausted ← IO.mkRef (#[] : Array String)
  let exhaustedNames ← IO.mkRef ({} : NameSet)
  let deepest ← IO.mkRef 0
  let longest ← IO.mkRef 0
  let axiomsOf : Name → IO (Array Name) := fun name => do
    let result := traverseAxioms environment axiomTraversalFuel (← memo.swap {}) name
    memo.set result.memo
    deepest.modify (max · result.depth)
    longest.modify (max · result.steps)
    match result.axioms? with
    | some axioms => return axioms
    | none =>
        unless (← exhaustedNames.get).contains name do
          exhaustedNames.modify (·.insert name)
          exhausted.modify (·.push
            s!"Whatwg axiom gate: the axiom traversal of {name} exhausted its fuel of {axiomTraversalFuel} steps")
        return #[]
  -- Every audited declaration first, in the order the in-tree command's
  -- `Lean.collectAxioms` tables were written (module by module, each module's
  -- constants in its own order), so that no pass's order of questions changes
  -- an answer around a dependency cycle.
  match auditedDeclarations config environment with
  | .ok declarations =>
      for declaration in declarations do
        discard <| axiomsOf declaration.name
  | .error message => throw <| IO.userError message
  let mark ← recordTiming state "axiom traversal" mark
  let passMark ← IO.mkRef mark
  let passIndex ← IO.mkRef 0
  let host : Host IO :=
    { axiomsOf
      report := fun findings => do
        emitFindings state (← exhausted.swap #[])
        emitFindings state findings
        let index ← passIndex.modifyGet fun index => (index, index + 1)
        let label := passLabels[index]?.getD s!"pass {index}"
        passMark.set (← recordTiming state label (← passMark.get)) }
  let summary? ← match ← (runPasses config host environment reads rootFile
      (← IO.FS.readFile rootFile)).run with
    | .ok summary? => pure summary?
    | .error message => throw <| IO.userError message
  emitFindings state (← exhausted.swap #[])
  let mark ← passMark.get
  IO.eprintln s!"NOTE whatwg_trustgate axiom traversal: {(← memo.get).size} constants closed, deepest stack {← deepest.get}, most steps in one traversal {← longest.get}, fuel {axiomTraversalFuel} steps per traversal"
  -- 5. The extension allowlist.
  emitFindings state (allowlistFindings config environment)
  let mark ← recordTiming state "extension allowlist" mark
  -- 6. The link closure.
  emitFindings state (← linkClosureFindings config environment projectRoot)
  let _ ← recordTiming state "link closure" mark
  -- 7. The verdict.
  verdict state summary?

/-- Command-line entry, invoked by `whatwgbin/TrustGate.lean` with this
repository's configuration. No argument is admitted. -/
def cli (config : Config) (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: lake exe whatwg_trustgate"
    return 2
  try
    runGate config
  catch error =>
    IO.eprintln s!"whatwg_trustgate: internal failure: {error}"
    return 2

end Gates.Trust
