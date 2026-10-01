import Lean.Environment
import Lean.Data.Json.Parser
import Lake.Build.Trace

/-!
# Gates.Trust.Load

The shared loader over built `.olean` files (addendum V2e.4 of
`test/contracts/trust-gate-hardening.contract.md`, ruling R-W7). The
executable trust gate `whatwg_trustgate`, the declaration snapshot
`whatwg_declsnapshot` and the graph ledger `whatwg_ledger` all read the built
tree through this module, so that they agree on which files they read, which
modules exist and which declarations each module owns.

## What it guarantees

- *Search path.* `initLoaderSearchPath root` sets `Lean.searchPathRef` to
  exactly `loaderSearchPath root (← Lean.findSysroot)`: the package's build
  directory `leanBuildDir root`, then the build directory of every directory
  under `<root>/.lake/packages` that has one, in ascending order of directory
  name, then `<sysroot>/lib/lean`. It never reads `LEAN_PATH`, so an audited
  module resolves to the built file whose trace `traceOf` reads, whoever
  launched the process.
- *Import.* `importBuilt modules` is `Lean.importModules` over exactly the
  given modules with `loadExts := false`. No environment extension's import
  hook runs, so no parser descriptor is evaluated and no `[init]` declaration
  of an imported module runs, and no plugin or dynamic library is loaded. The
  constant map, the module headers and every module's raw extension entries
  are available; every extension's *state* is its initial value.
- *Enumeration.* `sourceModules root trees` lists module sources from the file
  system, not from any import graph, so a module that nothing imports is still
  listed (debt D61). `moduleDeclarations env i` lists module `i`'s constants
  from its own `ModuleData.constNames`, keeping exactly those that
  `Environment.getModuleIdxFor?` attributes to `i`, which is the in-tree gate's
  read. `rawEntries` and `extensionsWithEntries` read `ModuleData.entries` by
  extension name and register nothing.
- *Freshness.* `traceOf buildRoot sourceRoot m` reads the `.trace` Lake wrote
  for `m`, and reports whether it names `m` and records as its source's hash
  the hash `Lake.computeTextFileHash` gives the source today, together with
  the `-D` options the trace records. It never throws.

## What it refuses

`parseTrace` refuses (returns `.error`) a text that is not JSON, has no
`inputs` array, has an `inputs` element that is not a `[label, value]` pair
with a string label, has no module-name element or more than one, no source
element or more than one, more than one `options`, `libs` or
`Module.leanArgs` element, an `options` or `libs` element that is not an array
of pairs of strings, a module-name element whose name does not read as a
module name, or a `Module.leanArgs` label that does not end in `]`.
`traceOf` turns every such refusal, a missing or unreadable trace and a
missing or unreadable source into `fresh = false`. `sourceModules` refuses
(throws) a tree name that is not a module name, an unreadable directory, and a
walk that exceeds `sourceWalkFuel` directory reads, which only a cycle of
symbolic links can cause. `importBuilt` throws for a requested name that is
not a module name, and whatever `Lean.importModules` throws: a module with no
built file, an unknown module prefix, a constant two modules both declare.

## Why extensions are not loaded

Loading extensions (`loadExts := true`) runs every imported module's
initializers and evaluates its parser descriptors in the reading process, and
needs `Lean.enableInitializersExecution`, which is `unsafe`. An audited module
could then replace or disable the very check that reads it, which is debt D56
of the in-tree command. This module never loads extensions, never calls
`enableInitializersExecution` or `evalConst`, and declares nothing `unsafe` or
`partial`; nothing an audited module wrote runs in a process that uses it.
Readers of a registration therefore read raw module entries, by extension name
(`rawEntries`), or through `getModuleEntries` of an extension the reading
process itself registered, whose imported entries `importModules` fills in
without loading the extension.

## What a caller must not conclude

- A fresh trace says that the source on disk is the one the trace records and
  that the trace names the module. It does not say that the `.olean` beside
  it exists (the caller checks that file itself), that the `.olean` is the one
  that build wrote, or that the module was compiled by an honest toolchain:
  a trace and a built file replaced together are not detected, and Lake, its
  trace hashing, `lean` and the `.olean` format stay trusted (V2e.7).
- The recorded options are the ones Lake traces: the package's and the
  library's `leanOptions` and the library's `moreLeanArgs`. `weakLeanArgs`,
  options passed to a `lean` run outside Lake and options a metaprogram sets
  leave no trace here.
- A synthetic trace (one Lake wrote when it fetched an artifact from a cache)
  records no inputs, so it does not parse and its module is never fresh.
- `importBuilt` re-checks nothing in the kernel; `leanchecker` stays the
  replay. Each call maps every built file it imports for the life of the
  process, so a caller imports once.

## Call sequence

1. `initLoaderSearchPath root`, once, before any import.
2. `sourceModules root trees`: the module sources, the root module included.
3. For each module `m`: `traceOf (leanBuildDir root) root m`, and the
   existence of `Lean.modToFilePath (leanBuildDir root) m "olean"`, which
   `traceOf` does not check. A caller that imports a module whose trace is not
   fresh reads a built file that is not its source's.
4. `importBuilt` over the modules the caller imports (the trust gate's import
   set never holds the root, V2e.1).
5. For each module index `i` below `env.header.moduleNames.size`:
   `moduleDeclarations env i`, `extensionsWithEntries env i` and
   `rawEntries env i e`.

`initLoaderSearchPath`, `sourceModules` and `importBuilt` throw on the
failures listed above; `parseTrace` returns its refusal as a value; `traceOf`
never throws; `moduleDeclarations`, `extensionsWithEntries` and `rawEntries`
are pure and answer `#[]` for an index out of range.
-/

namespace Gates.Trust

open Lean (Name Environment EnvExtensionEntry Json)

/-! ## Search path and import -/

/-- The directory Lake writes a package's built Lean files to:
`<root>/.lake/build/lib/lean`. -/
def leanBuildDir (root : System.FilePath) : System.FilePath :=
  root / ".lake" / "build" / "lib" / "lean"

/-- The loader's search path: the package's build directory; then the build
directory of every directory under `<root>/.lake/packages`, in ascending order
of directory name, each only if it exists; then `<sysroot>/lib/lean`. -/
def loaderSearchPath (root sysroot : System.FilePath) : IO System.SearchPath := do
  let packagesDirectory := root / ".lake" / "packages"
  let mut dependencies : Array System.FilePath := #[]
  if ← packagesDirectory.isDir then
    let entries := (← packagesDirectory.readDir).qsort fun left right =>
      left.fileName < right.fileName
    for entry in entries do
      if ← entry.path.isDir then
        let buildDirectory := leanBuildDir entry.path
        if ← buildDirectory.isDir then
          dependencies := dependencies.push buildDirectory
  return [leanBuildDir root] ++ dependencies.toList ++ [sysroot / "lib" / "lean"]

/-- Set `Lean.searchPathRef` to exactly `loaderSearchPath root (← Lean.findSysroot)`,
ignoring `LEAN_PATH`. Throws when the system root cannot be found or the
packages directory cannot be read. -/
def initLoaderSearchPath (root : System.FilePath) : IO Unit := do
  Lean.searchPathRef.set (← loaderSearchPath root (← Lean.findSysroot))

/-- Whether every component of a name is a non-empty string, so that
`Lean.modToFilePath` maps it to a path; the anonymous name is no module. Read
through `Lean.Name.componentsRev`, so this module defines no recursive
function. -/
def isModuleName (name : Name) : Bool :=
  !name.isAnonymous && name.componentsRev.all fun component =>
    match component with
    | .str .anonymous text => !text.isEmpty
    | _ => false

/-- Import the built files of `modules`, and of everything they import, with
no environment extension loaded:
`Lean.importModules (modules.map ({ module := · })) {} (loadExts := false)`,
so no import hook, parser descriptor or initializer of an imported module
runs. Call `initLoaderSearchPath` first. Throws when a module has no built
file or two modules declare one constant, and, before importing anything,
when a requested name is not a module name (for which `Lean.modToFilePath`
would panic). -/
def importBuilt (modules : Array Name) : IO Environment := do
  if let some bad := modules.find? (!isModuleName ·) then
    throw <| IO.userError s!"Whatwg trust loader: cannot import {bad}, which is not a module name"
  Lean.importModules (modules.map ({ module := · })) {} (loadExts := false)

/-! ## Module sources -/

/-- Whether a path names a Lean source: its extension is `lean` in any case,
as the in-tree gate reads it, so that a `.LEAN` file a case-insensitive host
builds is listed rather than skipped. -/
def isLeanSourcePath (path : System.FilePath) : Bool :=
  match path.extension with
  | some extension => extension.toLower == "lean"
  | none => false

/-- Directory reads one tree's walk may make. A tree has a few dozen
directories, so exhaustion means a cycle of symbolic links. -/
def sourceWalkFuel : Nat := 100000

/-- The module of every Lean source below `directory`, whose own module name is
`directoryModule`: each file's path below `directory` read as a module name,
one component per directory and the file's stem as the last, as
`Lean.forEachModuleInDir` reads it. Symbolic links to directories are followed
under the link's own name; the walk is bounded by `sourceWalkFuel` reads. -/
def leanModulesBelow (directory : System.FilePath) (directoryModule : Name) :
    IO (Array Name) := do
  let mut pending : Array (System.FilePath × Name) := #[(directory, directoryModule)]
  let mut found : Array Name := #[]
  for _ in [0:sourceWalkFuel] do
    match pending.back? with
    | none => return found
    | some (current, currentModule) =>
      pending := pending.pop
      for entry in ← current.readDir do
        if ← entry.path.isDir then
          pending := pending.push (entry.path, .str currentModule entry.fileName)
        else if isLeanSourcePath entry.path then
          if let some stem := entry.path.fileStem then
            found := found.push (.str currentModule stem)
  if pending.isEmpty then
    return found
  throw <| IO.userError
    s!"Whatwg trust loader: the walk below {directory} exceeded {sourceWalkFuel} directory reads"

/-- The module sources of `trees` below `root`: for each tree `t`, the module
`t` when the file `t.lean` exists below `root`, then the module of every file
below the directory of `t` whose extension is `lean` in any case. The result
is in ascending order of each module name's string, each module once. -/
def sourceModules (root : System.FilePath) (trees : List Name) : IO (Array Name) := do
  let mut found : Array Name := #[]
  for tree in trees do
    unless isModuleName tree do
      throw <| IO.userError s!"Whatwg trust loader: the tree {tree} is not a module name"
    let treeSource := Lean.modToFilePath root tree "lean"
    if (← treeSource.pathExists) && !(← treeSource.isDir) then
      found := found.push tree
    let treeDirectory := Lean.modToFilePath root tree ""
    if ← treeDirectory.isDir then
      found := found ++ (← leanModulesBelow treeDirectory tree)
  let sorted := (found.map fun name => (name.toString, name)).qsort fun left right =>
    left.1 < right.1
  let mut modules : Array Name := #[]
  for (_, name) in sorted do
    if modules.back? != some name then
      modules := modules.push name
  return modules

/-! ## Declarations and raw extension entries -/

/-- Module `index`'s constants, from its own `ModuleData.constNames` in order,
keeping exactly those `Environment.getModuleIdxFor?` attributes to `index`; a
constant several modules realise counts once, in the module the environment
records. Empty for an index out of range. -/
def moduleDeclarations (environment : Environment) (index : Nat) : Array Name :=
  match environment.header.moduleData[index]? with
  | none => #[]
  | some data =>
      data.constNames.filter fun name =>
        (environment.getModuleIdxFor? name).map (·.toNat) == some index

/-- The entries module `index` records under the extension named `extension` in
its `ModuleData.entries`, read without registering or loading the extension;
empty when it records none or the index is out of range. Lean's writer records
each extension once; should a built file record one twice, every array
recorded under the name is returned, in order, so that no recorded entry is
hidden from the caller. -/
def rawEntries (environment : Environment) (index : Nat) (extension : Name) :
    Array EnvExtensionEntry :=
  match environment.header.moduleData[index]? with
  | none => #[]
  | some data =>
      data.entries.foldl (init := #[]) fun found (name, entries) =>
        if name == extension then found ++ entries else found

/-- Every extension name under which module `index` records a non-empty entry
array, with the number of entries, in the order of `ModuleData.entries`; each
name once, with the size `rawEntries` returns for it. Empty for an index out
of range. -/
def extensionsWithEntries (environment : Environment) (index : Nat) :
    Array (Name × Nat) :=
  match environment.header.moduleData[index]? with
  | none => #[]
  | some data => Id.run do
      let mut listed : Array (Name × Nat) := #[]
      for (name, entries) in data.entries do
        if entries.isEmpty then
          continue
        match listed.findIdx? (·.1 == name) with
        | some position =>
            listed := listed.modify position fun (listedName, count) =>
              (listedName, count + entries.size)
        | none =>
            listed := listed.push (name, entries.size)
      return listed

/-! ## Lake traces -/

/-- What one module's `.trace` records, read from the elements of its
top-level `inputs` array. -/
structure TraceRecord where
  /-- The rest of the label of the element whose label begins `Module.name: `. -/
  moduleName : Name
  /-- The value of the one element whose label ends in `.lean` and whose value
  is a string: the source's hash when Lake built the module. -/
  sourceHash : String
  /-- The first component of each pair of the element labelled `options`, in
  order: the package's and the library's `leanOptions` as `-D` arguments. -/
  options : Array String
  /-- The arguments of the element whose label begins `Module.leanArgs: #[`:
  the text between `#[` and the final `]`, split at `, `. -/
  leanArgs : Array String
  /-- Each pair of the element labelled `libs`, as label and value. -/
  libs : Array (String × String)
  deriving Inhabited, BEq, Repr

/-- The recorded options: `options`, then every `leanArgs` argument that
begins `-D`. -/
def TraceRecord.recordedOptions (record : TraceRecord) : Array String :=
  record.options ++ record.leanArgs.filter (·.startsWith "-D")

/-- A JSON array of `[string, string]` pairs, or `none`. -/
def stringPairs? : Json → Option (Array (String × String))
  | .arr items =>
      items.mapM fun item =>
        match item with
        | .arr #[.str first, .str second] => some (first, second)
        | _ => none
  | _ => none

/-- The label after `Module.name: ` read as a module name, or `none`. -/
def traceModuleName? (rest : String) : Option Name :=
  let name := rest.toName
  if isModuleName name then some name else none

/-- The arguments of a `Module.leanArgs: #[…]` label, given the text after
`#[`: the text before the final `]` split at `, `, empty for `#[]`; `none`
when the label does not end in `]`. -/
def traceLeanArgs? (afterBracket : String) : Option (Array String) :=
  match afterBracket.dropSuffix? "]" with
  | none => none
  | some inner =>
      let text := inner.copy
      if text.isEmpty then some #[] else some (text.splitOn ", ").toArray

/-- Read a Lake trace (addendum V2e.4, item 5). Each element of the top-level
`inputs` array is a `[label, value]` pair, classified in this order: the label
`options`; the label `libs`; a label that begins `Module.name: `; a label that
begins `Module.leanArgs: #[`; otherwise a label that ends in `.lean` with a
string value, the source element. The module-name element and the source
element must each occur exactly once; the other three at most once, and an
absent one reads as empty. -/
def parseTrace (text : String) : Except String TraceRecord := do
  let json ← match Json.parse text with
    | .ok json => pure json
    | .error reason => throw s!"the trace is not JSON: {reason}"
  let inputs ← match json.getObjVal? "inputs" with
    | .ok (.arr inputs) => pure inputs
    | _ => throw "the trace has no inputs array"
  let mut moduleNames : Array Name := #[]
  let mut sourceHashes : Array String := #[]
  let mut optionElements : Array (Array String) := #[]
  let mut leanArgElements : Array (Array String) := #[]
  let mut libElements : Array (Array (String × String)) := #[]
  for input in inputs do
    let .arr #[.str label, value] := input
      | throw "an element of the trace's inputs is not a [label, value] pair"
    if label == "options" then
      let some pairs := stringPairs? value
        | throw "the trace's options element is not an array of pairs of strings"
      optionElements := optionElements.push (pairs.map (·.1))
    else if label == "libs" then
      let some pairs := stringPairs? value
        | throw "the trace's libs element is not an array of pairs of strings"
      libElements := libElements.push pairs
    else if let some rest := label.dropPrefix? "Module.name: " then
      let some name := traceModuleName? rest.copy
        | throw s!"the trace's module-name element names no module: {label}"
      moduleNames := moduleNames.push name
    else if let some rest := label.dropPrefix? "Module.leanArgs: #[" then
      let some arguments := traceLeanArgs? rest.copy
        | throw s!"the trace's leanArgs element does not end in ]: {label}"
      leanArgElements := leanArgElements.push arguments
    else if label.endsWith ".lean" then
      if let .str hash := value then
        sourceHashes := sourceHashes.push hash
  let moduleName ← match moduleNames with
    | #[name] => pure name
    | #[] => throw "the trace has no module-name element"
    | _ => throw "the trace has more than one module-name element"
  let sourceHash ← match sourceHashes with
    | #[hash] => pure hash
    | #[] => throw "the trace has no source element"
    | _ => throw "the trace has more than one source element"
  let options ← match optionElements with
    | #[] => pure #[]
    | #[options] => pure options
    | _ => throw "the trace has more than one options element"
  let leanArgs ← match leanArgElements with
    | #[] => pure #[]
    | #[arguments] => pure arguments
    | _ => throw "the trace has more than one leanArgs element"
  let libs ← match libElements with
    | #[] => pure #[]
    | #[pairs] => pure pairs
    | _ => throw "the trace has more than one libs element"
  return { moduleName, sourceHash, options, leanArgs, libs }

/-- The source hash of a file as Lake records it in a trace:
`Lake.computeTextFileHash` (line endings normalised to `\n`), printed as
sixteen lowercase hexadecimal digits. Throws when the file cannot be read. -/
def sourceHash (file : System.FilePath) : IO String := do
  return (← Lake.computeTextFileHash file).toString

/-- Freshness and recorded options of module `moduleName` (addendum V2e.4,
item 6): `(false, #[])` when the name is no module name, or the trace
`Lean.modToFilePath buildRoot moduleName "trace"` is missing, unreadable or
does not parse; otherwise `(fresh, record.recordedOptions)`, where `fresh`
holds when the record names `moduleName` and records the source hash of
`Lean.modToFilePath sourceRoot moduleName "lean"` (false when that source
cannot be read). It never throws, and it does not look at the `.olean`. -/
def traceOf (buildRoot sourceRoot : System.FilePath) (moduleName : Name) :
    IO (Bool × Array String) := do
  unless isModuleName moduleName do
    return (false, #[])
  match ← (IO.FS.readFile (Lean.modToFilePath buildRoot moduleName "trace")).toBaseIO with
  | .error _ => return (false, #[])
  | .ok text =>
      match parseTrace text with
      | .error _ => return (false, #[])
      | .ok record =>
          let current ←
            (sourceHash (Lean.modToFilePath sourceRoot moduleName "lean")).toBaseIO
          let fresh := match current with
            | .ok hash => record.moduleName == moduleName && hash == record.sourceHash
            | .error _ => false
          return (fresh, record.recordedOptions)

end Gates.Trust
