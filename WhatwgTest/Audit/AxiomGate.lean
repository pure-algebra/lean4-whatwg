import Lean
import Lean.Util.CollectAxioms
import Whatwg
import Gates

/-!
# Whatwg trust and axiom gate

`#whatwg_streams_axiom_gate`, run last by the test root `WhatwgTest.lean`,
decides where trust enters the repository. It reads two things: every authored
source under `Whatwg/`, `WhatwgTest/`, `Gates/` and `bin/` with the three roots,
and every constant of every audited module in the compiled environment,
authored, private, auxiliary and Lean-generated alike. Its behaviour is frozen
by `test/contracts/trust-gate-hardening.contract.md` (rulings R-V1 and R-V2) and
falsified by `lake exe trustselftest`.

## Passes, in order

The gate runs five passes in the order the contract's section 3 fixes. Each
pass reports every finding it has, one error per finding, and the gate stops
after the first pass that has any, so the order decides which pass reports a
plant two passes would refuse.

1. *Module closure.* Every module source is imported by the test root. `bin/`
   is excluded: its files are executable roots no audit root imports.
2. *Modifier pass.* An authored `unsafe` or `partial` keyword in code, in any
   audited source, `bin/` included, is refused; so is a source the tokenizer
   cannot read to its end.
3. *Environment pass.* Over every constant of an audited module, apart from a
   generated safe recursor: an `unsafe` or `partial` constant, a declared
   axiom (a native-evaluation auxiliary named as such), an `@[extern]` or
   `@[implemented_by]` constant, and an `opaque` whose value Lean synthesised.
4. *Axiom pass.* `Lean.collectAxioms` over the same constants. `sorryAx`,
   `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and every
   native-evaluation auxiliary are forbidden everywhere. Ruling R-11's ceiling,
   `propext`, `Quot.sound` and `Classical.choice`, binds every audited tree.
   Ruling R-V1's strict ceiling, `propext` and `Quot.sound` only, binds every
   constant whose module is under a prefix of `strictCeilingPrefixes`, unless an
   exact entry of `strictCeilingExceptions` or `privateStrictCeilingExceptions`
   names it; every entry is checked for need.
5. *Trust-token pass.* A token of code that carries a word of `refusedWords`,
   in any audited source, is refused unless the source's module has an exact
   entry in `sourceTokenExemptions`; every entry is checked for need.

A successful run logs one summary line with the per-tree counts of
declarations that reach `Classical.choice`.

## Two ceilings, one structure

Before R-V1 the gate held two ceilings with the same three axioms, a
"semantic" one and an "implementation" one, and an audit-module list with a
staleness check that justified nothing once R-11 admitted `Classical.choice`
everywhere. They are collapsed: R-11's ceiling binds everything, and the strict
ceiling is the only narrower bound, chosen by module prefix and relaxed only by
exact declaration. Strictness is decided by the module `getModuleIdxFor?`
records for a constant, never by its name, so a declaration cannot leave the
strict ceiling by its namespace, and an equation lemma counts in the module
that minted it. An exception admits its own declaration and nothing else: an
excepted declaration's auxiliaries need entries of their own.

## What the passes read

The source passes are lexical. Lean's own tokenizer, with the token table of
the final environment, splits each source; comments, documentation comments,
module documentation, and every literal (string, raw string, interpolated
string, character, numeric and name literals) are not code. A keyword carries a
word when its text is the word; an identifier when its `Name`, escapes removed,
equals the word's `Name`, or, for a forbidden axiom, when its last component is
the axiom's short name. So `axioms` (the receipt command's word), `externals`
and `Foo.native` are names, and `«sorry»` is refused like `sorry`. This module
spells every refused word as a string literal and every axiom as a name
literal, so it needs no exemption of its own.

`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for the source passes; the environment pass independently confirms
what the compiled constants are.

Section 13 of the contract states what a green gate does not mean: a name built
by metaprogramming, an option set outside the source, and a macro defined
outside the audited trees are invisible to the token pass, and `bin/` is read
by the source passes only.

This gate began as a port of lean4-effect4's `Effect4Test/Audit/AxiomGate.lean`;
the environment pass follows that gate at `0f16828a`, as R-V2 directs.
-/

open Lean

namespace WhatwgTest.Audit

/-! ## Ceilings and their lists -/

/-- Ruling R-11's ceiling, Lean's standard base, binding every audited tree. -/
private def repositoryCeiling : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/-- Ruling R-V1's strict ceiling, binding every constant whose module is under a
prefix of `strictCeilingPrefixes`. -/
private def strictCeiling : List Name :=
  [``propext, ``Quot.sound]

/-- A ceiling as its diagnostics spell it, on one line. -/
private def ceilingText (separator : String) (ceiling : List Name) : String :=
  separator.intercalate (ceiling.map toString)

/-- Module prefixes under the strict ceiling (ruling R-V1). A prefix joins when
its measured residue, the constants under it that reach `Classical.choice`, is
zero or wholly covered by exact exceptions the coordinator accepts as debts.
Adding a prefix is one line; the build then fails with one error per residue
declaration, which is the measurement.

At the V2 landing the four prefixes below have zero residue. `Whatwg.Streams`
joins at integration with the R-V5 repair. `Whatwg.Html.Print` and the
`String`-borne definitions of `Whatwg.Infra.{Namespaces,Text.Scalar,Text.String}`
stay under R-11: they reach `Classical.choice` through core's `String` API. A
prefix must lie inside the `Whatwg` tree, since R-V1 keeps `WhatwgTest` and
`Gates` under R-11, and must cover at least one audited module, so that a
misspelt prefix cannot make the strict ceiling vacuous. -/
private def strictCeilingPrefixes : List Name :=
  [ `Whatwg.Ecma262
  , `Whatwg.WebIdl
  , `Whatwg.Url
  , `Whatwg.Infra.Text.Utf8
  ]

/-- An exact admission of one declaration under the strict ceiling to
`Classical.choice`, with the reason the coordinator accepted it as a debt. -/
private structure StrictCeilingException where
  declaration : Name
  reason : String

/-- Exact strict-ceiling exceptions, one declaration each, written
`` ⟨`Full.Name, "reason"⟩ :: `` on its own line below the anchor comment, where
`lake exe trustselftest` plants its entries too. The gate refuses an entry that
names no declaration, one whose module is under no strict prefix, one whose
declaration does not reach `Classical.choice`, one with a blank reason, and one
listed twice. Empty at the V2 landing. -/
private def strictCeilingExceptions : List StrictCeilingException :=
  -- trust-selftest: strict-ceiling exception entries are inserted below this line
  []

/-- A strict-ceiling exception for a private declaration, identified by its
exact owning module and its original spelling, never by Lean's private-name
counter. -/
private structure PrivateStrictCeilingException where
  owner : Name
  original : Name
  reason : String

/-- Private strict-ceiling exceptions. Each must resolve to exactly one audited
declaration and then passes the same checks as `strictCeilingExceptions`.
Empty at the V2 landing. -/
private def privateStrictCeilingExceptions : List PrivateStrictCeilingException :=
  []

/-- An exact admission of one module's source to the trust-token pass, and to
no other check, with the reason it must name a refused word in code. -/
private structure SourceTokenExemption where
  moduleName : Name
  reason : String

/-- Source-token exemptions by exact module name, written
`` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor comment. The
gate refuses an entry that names no audited module source, one that names an
entry point under `bin/` (none can be exempted), one whose source carries no
refused word in code, one with a blank reason, and one listed twice. Empty at
the V2 landing: this module spells its word lists as literals. -/
private def sourceTokenExemptions : List SourceTokenExemption :=
  -- trust-selftest: source-token exemption entries are inserted below this line
  []

/-- The three forbidden axioms the trust-token pass also refuses by name. -/
private def forbiddenTrustAxioms : List Name :=
  [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Axioms no audited constant may reach. -/
private def forbiddenAxioms : List Name :=
  ``sorryAx :: forbiddenTrustAxioms

/-- `native_decide` mints a per-declaration auxiliary axiom whose name carries a
`_native` component (Lean 4.33.1 records `t._native.native_decide.ax_1_1` for a
theorem `t`). Such an axiom is forbidden by shape, whatever declaration it
hangs off. -/
private def isNativeAuxiliaryAxiom (axiomName : Name) : Bool :=
  axiomName.anyS fun component => component == "_native"

/-- The synthesised values Lean gives an `opaque` with no body
(`default_or_ofNonempty%`, `Lean/Elab/DefView.lean`). -/
private def synthesizedOpaqueBodies : List Name :=
  [``Inhabited.default, ``Classical.ofNonempty]

/-! ## Trees, modules and declarations -/

/-- The audited trees, disjoint under `Name.isPrefixOf`, which compares whole
components. The SHA-256 lane that used to be a fourth is the required `hash`
package since step 6 of `docs/HASH-PACKAGE-PLAN.md`; its own gate audits it
there, and nothing under a dependency is inspected here. -/
private def auditedTrees : List Name :=
  [`Whatwg, `WhatwgTest, `Gates]

private def treeOf? (moduleName : Name) : Option Name :=
  auditedTrees.find? (·.isPrefixOf moduleName)

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

/-- The strict prefix a module is under: the longest that matches, if any. -/
private def strictPrefixOf? (moduleName : Name) : Option Name :=
  strictCeilingPrefixes.foldl (init := none) fun best candidate =>
    if candidate.isPrefixOf moduleName then
      match best with
      | some current => if current.getNumParts < candidate.getNumParts then some candidate else best
      | none => some candidate
    else best

/-- One constant of an audited module. -/
private structure AuditedDeclaration where
  name : Name
  moduleName : Name
  tree : Name

/-- Every constant of every audited module, read from the modules' own constant
lists rather than by materialising the whole constant map. A constant that
more than one module realises (an equation lemma that several modules unfold)
appears once, under the module `getModuleIdxFor?` records, exactly as the
environment's constant map holds it once. -/
private def auditedDeclarations (environment : Environment) :
    Except String (Array AuditedDeclaration) := do
  let header := environment.header
  if header.moduleNames.size != header.moduleData.size then
    throw s!"Whatwg trust gate: the environment records {header.moduleNames.size} module names and {header.moduleData.size} module data entries"
  let mut found : Array AuditedDeclaration := #[]
  for index in [0:header.moduleNames.size] do
    let some moduleName := header.moduleNames[index]?
      | throw s!"Whatwg trust gate: module index {index} has no name"
    let some tree := treeOf? moduleName | continue
    let some data := header.moduleData[index]?
      | throw s!"Whatwg trust gate: audited module {moduleName} has no module data"
    for name in data.constNames do
      if (environment.getModuleIdxFor? name).map (·.toNat) == some index then
        found := found.push { name, moduleName, tree }
  return found

private def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

/-- The body under every leading `fun` binder and metadata wrapper. -/
private def lambdaBody : Expr → Expr
  | .lam _ _ body _ => lambdaBody body
  | .mdata _ inner => lambdaBody inner
  | value => value

/-- Whether an `opaque` value is the one Lean synthesised for a missing body:
its head constant, under the binders a parameterised `opaque` puts in front,
is `Inhabited.default` or `Classical.ofNonempty`. An authored body that is
literally `default` is refused with them, by design (contract section 4.1). -/
private def isSynthesizedOpaqueBody (value : Expr) : Bool :=
  match (lambdaBody value).getAppFn with
  | .const name _ => synthesizedOpaqueBodies.contains name
  | _ => false

/-- Whether a string is empty after trimming ASCII whitespace. -/
private def isBlank (text : String) : Bool :=
  text.toList.all Char.isWhitespace

/-! ## Source tokens -/

/-- A word the trust-token pass refuses (contract section 4.2). -/
private structure RefusedWord where
  /-- The word as a diagnostic prints it. -/
  printed : String
  /-- The `Name` an identifier must equal, escapes removed, to carry the word. -/
  name : Name
  /-- For a forbidden axiom, the short name: an identifier whose last component
  it is carries the word as well. -/
  lastComponent? : Option String := none

private def lastStringComponent? : Name → Option String
  | .str _ component => some component
  | _ => none

/-- A dotted spelling as a `Name`, one component per dot. -/
private def dottedName (text : String) : Name :=
  (text.splitOn ".").foldl Name.mkStr Name.anonymous

private def refusedWord (printed : String) : RefusedWord :=
  { printed, name := dottedName printed }

private def refusedAxiomWord (axiomName : Name) : RefusedWord :=
  { printed := axiomName.toString, name := axiomName,
    lastComponent? := lastStringComponent? axiomName }

/-- The words that open a trust channel no constant records (ruling R-V2), each
refused as a keyword and as an identifier: compiler evaluation (`native_decide`,
`bv_decide`, `bv_decide?`, `bv_check`, and the `native` configuration flag in
every spelling), an admitted goal, an assumption, a replaced body, a
declaration the kernel never checks, and the three forbidden axioms by name. -/
private def refusedWords : List RefusedWord :=
  ["native_decide", "bv_decide", "bv_decide?", "bv_check", "native", "sorry", "axiom",
    "implemented_by", "extern", "debug.skipKernelTC"].map refusedWord ++
  forbiddenTrustAxioms.map refusedAxiomWord

/-- Whether one token of code carries the word. -/
private def RefusedWord.carriedBy (word : RefusedWord) : Syntax → Bool
  | .atom _ text => text == word.printed || word.lastComponent? == some text
  | .ident _ _ name _ =>
      name == word.name ||
        (word.lastComponent?.isSome && lastStringComponent? name == word.lastComponent?)
  | _ => false

/-- The declaration modifiers the modifier pass refuses, as keywords only:
`«unsafe»` and `«partial»` stay names. -/
private def modifierWords : List String :=
  ["unsafe", "partial"]

/-- One refused token of one source, at a one-based line and column. -/
private structure TokenHit where
  word : String
  line : Nat
  column : Nat

/-- What the tokenizer found in one audited source. -/
private structure SourceScan where
  source : System.FilePath
  modifiers : Array TokenHit := #[]
  trustTokens : Array TokenHit := #[]
  /-- Why the tokenizer stopped before the end of the source, if it did. -/
  failure? : Option String := none

/-- Tokenize one source with Lean's own tokenizer and record every modifier
keyword and every refused trust token in code. Documentation comments and
module documentation are syntax nodes rather than whitespace, so Lean's own
parsers consume them and their prose never becomes tokens. Each round consumes
at least one byte or ends the scan, so the byte count bounds the rounds; a round
that consumes nothing, or a source that outlasts its rounds, is a failure,
never a silent end. -/
private def scanSource (environment : Environment) (tokenTable : Parser.TokenTable)
    (source : System.FilePath) : IO SourceScan := do
  let input ← IO.FS.readFile source
  let inputContext := Parser.mkInputContext input source.toString
  let parserContext : Parser.ParserModuleContext :=
    { env := environment, options := {} }
  let fail (pos : String.Pos.Raw) (reason : String) : String :=
    let position := inputContext.fileMap.toPosition pos
    s!"Whatwg source trust gate: tokenization failed in {source}:{position.line}:{position.column + 1}: {reason}"
  let mut scan : SourceScan := { source }
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  let rounds := input.utf8ByteSize + 1
  for _ in [0:rounds] do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      return { scan with failure? := some (fail state.pos (toString error)) }
    state := skipped
    if inputContext.atEnd state.pos then
      return scan
    let start := state.pos
    let docComment := Parser.Command.docComment.fn.run
      inputContext parserContext tokenTable state
    if docComment.errorMsg.isNone then
      state := docComment.popSyntax
      projectionEnd := none
    else
      let moduleDoc := Parser.Command.moduleDoc.fn.run
        inputContext parserContext tokenTable state
      if moduleDoc.errorMsg.isNone then
        state := moduleDoc.popSyntax
        projectionEnd := none
      else
        -- Lean parses the index in `h.2.trans` and `h |>.2.trans` with
        -- `fieldIdxFn`: the ordinary number tokenizer mistakes `2.trans` for a
        -- decimal. Use the same parser only immediately after a projection dot;
        -- ordinary numerals and every tokenization error retain their usual path.
        let tokenParser :=
          if projectionEnd == some state.pos && (inputContext.get state.pos).isDigit then
            Parser.fieldIdxFn
          else
            Parser.tokenFn []
        let next := tokenParser.run inputContext parserContext tokenTable state
        if let some error := next.errorMsg then
          return { scan with failure? := some (fail state.pos (toString error)) }
        let token := next.stxStack.back
        let position := inputContext.fileMap.toPosition start
        let hit (word : String) : TokenHit :=
          { word, line := position.line, column := position.column + 1 }
        if let some modifier := modifierWords.find? (token.isToken ·) then
          scan := { scan with modifiers := scan.modifiers.push (hit modifier) }
        for word in refusedWords do
          if word.carriedBy token then
            scan := { scan with trustTokens := scan.trustTokens.push (hit word.printed) }
        projectionEnd :=
          if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
        state := next.popSyntax
    unless start.byteIdx < state.pos.byteIdx do
      return { scan with failure? := some (fail start "the tokenizer consumed nothing") }
  return { scan with failure? := some (fail state.pos s!"the scan did not end within {rounds} rounds") }

/-! ## Sources -/

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Whatwg.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Whatwg axiom gate: could not locate the project root"
  throw <| IO.userError "Whatwg axiom gate: project-root search exceeded 64 parents"

/-- The gate's own source as an absolute path. `lake build` hands the
elaborator an absolute file name; `lake env lean WhatwgTest.lean` hands it the
relative one, whose parent walk ends before the root. A relative name is joined
to the working directory first (contract section 11). -/
private def absoluteSourcePath (named : System.FilePath) : IO System.FilePath := do
  if named.isAbsolute then
    return named
  return (← IO.currentDir) / named

private def leanFilesBelow (directory : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← directory.walkDir
  return (entries.filter fun path => path.extension == some "lean").qsort
    fun left right => left.toString < right.toString

/-- The audited sources: module sources, which the test root must import, and
executable entry points under `bin/`, which no audit root imports and which the
source passes alone read. -/
private structure AuditedSources where
  modules : Array System.FilePath
  entryPoints : Array System.FilePath

private def auditedSources (projectRoot : System.FilePath) : IO AuditedSources := do
  let production ← leanFilesBelow (projectRoot / "Whatwg")
  let tests ← leanFilesBelow (projectRoot / "WhatwgTest")
  let tooling ← leanFilesBelow (projectRoot / "Gates")
  let entryPoints ← leanFilesBelow (projectRoot / "bin")
  let roots :=
    #[projectRoot / "Whatwg.lean", projectRoot / "Gates.lean", projectRoot / "WhatwgTest.lean"]
  return { modules := production ++ tests ++ tooling ++ roots, entryPoints }

/-! ## The passes -/

open Elab Command

/-- Log every finding of one pass as its own error, and say whether there was
none. -/
private def reportFindings (findings : Array MessageData) : CommandElabM Bool := do
  for finding in findings do
    logError finding
  return findings.isEmpty

/-- Pass 2: tokenization failures and the `unsafe` and `partial` keywords. -/
private def modifierFindings (scans : Array SourceScan) : Array MessageData :=
  scans.flatMap fun scan =>
    let failures := match scan.failure? with
      | some failure => #[m!"{failure}"]
      | none => #[]
    failures ++ scan.modifiers.map fun hit =>
      m!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` declaration modifier at line {hit.line}, column {hit.column}"

/-- Pass 3: what each audited constant is (contract section 4.1). -/
private def environmentFindings (environment : Environment)
    (declarations : Array AuditedDeclaration) : Array MessageData := Id.run do
  let mut findings : Array MessageData := #[]
  for declaration in declarations do
    let name := declaration.name
    if isGeneratedSafeRecursor environment name then continue
    let info ← match environment.find? name with
      | some info => pure info
      | none =>
          findings := findings.push
            m!"Whatwg trust gate: declaration {name} of module {declaration.moduleName} is missing from the environment"
          continue
    if info.isUnsafe then
      findings := findings.push m!"Whatwg trust gate: declaration {name} is unsafe"
    if info.isPartial then
      findings := findings.push m!"Whatwg trust gate: declaration {name} is partial"
    if let .axiomInfo _ := info then
      if isNativeAuxiliaryAxiom name then
        findings := findings.push
          m!"Whatwg trust gate: declaration {name} is a native-evaluation axiom (native_decide auxiliary)"
      else
        findings := findings.push
          m!"Whatwg trust gate: declaration {name} is an axiom; no audited tree declares one"
    if isExtern environment name then
      findings := findings.push
        m!"Whatwg trust gate: declaration {name} is `@[extern]`; host code replaces its checked body"
    if (Compiler.getImplementedBy? environment name).isSome then
      findings := findings.push
        m!"Whatwg trust gate: declaration {name} is `@[implemented_by]`; another declaration replaces its checked body in compiled code"
    if let .opaqueInfo opaqueInfo := info then
      if isSynthesizedOpaqueBody opaqueInfo.value then
        findings := findings.push
          m!"Whatwg trust gate: declaration {name} is an `opaque` with no authored body; Lean synthesised its value, so it denotes an inhabitant nobody chose"
  return findings

/-- The checks every strict-ceiling exception passes once it names a
declaration (contract section 6): its module is under a strict prefix, and it
reaches `Classical.choice`. -/
private def strictExceptionTargetFindings (environment : Environment) (declaration : Name) :
    CommandElabM (Array MessageData) := do
  if !environment.contains declaration then
    return #[m!"Whatwg axiom gate: strict-ceiling exception names missing declaration {declaration}"]
  let moduleName := (moduleOf? environment declaration).getD environment.mainModule
  if (strictPrefixOf? moduleName).isNone then
    return #[m!"Whatwg axiom gate: stale strict-ceiling exception for {declaration}; its module {moduleName} is under no strict prefix"]
  if !(← collectAxioms declaration).contains ``Classical.choice then
    return #[m!"Whatwg axiom gate: stale strict-ceiling exception for {declaration}; it does not reach Classical.choice"]
  return #[]

/-- Validate the strict prefixes and every strict-ceiling exception; return the
findings and the declarations the exceptions name. -/
private def strictCeilingFindings (environment : Environment)
    (declarations : Array AuditedDeclaration) :
    CommandElabM (Array MessageData × Array Name) := do
  let mut findings : Array MessageData := #[]
  for strictPrefix in strictCeilingPrefixes do
    if !(`Whatwg).isPrefixOf strictPrefix then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling prefix {strictPrefix} is outside the Whatwg tree; ruling R-V1 keeps WhatwgTest and Gates under R-11"
    if !(declarations.any fun declaration => strictPrefix.isPrefixOf declaration.moduleName) then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling prefix {strictPrefix} covers no audited module"
  let mut excepted : Array Name := #[]
  for entry in strictCeilingExceptions do
    if isBlank entry.reason then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling exception for {entry.declaration} carries no reason"
    findings := findings ++ (← strictExceptionTargetFindings environment entry.declaration)
    excepted := excepted.push entry.declaration
  for entry in privateStrictCeilingExceptions do
    if isBlank entry.reason then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling exception for {entry.original} (private to {entry.owner}) carries no reason"
    let owned := declarations.filter fun declaration =>
      declaration.moduleName == entry.owner &&
        privateToUserName? declaration.name == some entry.original
    match owned.toList with
    | [declaration] =>
        findings := findings ++ (← strictExceptionTargetFindings environment declaration.name)
        excepted := excepted.push declaration.name
    | [] =>
        findings := findings.push
          m!"Whatwg axiom gate: strict-ceiling exception names missing declaration {entry.original} (private to {entry.owner})"
    | _ =>
        findings := findings.push
          m!"Whatwg axiom gate: private strict-ceiling exception {entry.owner}/{entry.original} matched {owned.size} declarations; expected exactly one"
  let mut seen : NameSet := {}
  let mut repeated : NameSet := {}
  for name in excepted do
    if seen.contains name && !repeated.contains name then
      repeated := repeated.insert name
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling exception for {name} is listed more than once"
    seen := seen.insert name
  return (findings, excepted)

/-- Pass 5: validate the exemption list, then refuse every refused token outside
an exempted source and every exemption whose source needs none (contract
sections 4.2 and 4.3). -/
private def trustTokenFindings (projectRoot : System.FilePath) (sources : AuditedSources)
    (scans : Array SourceScan) : Array MessageData := Id.run do
  let mut findings : Array MessageData := #[]
  let modulePaths := sources.modules.map (·.normalize)
  let entryPaths := sources.entryPoints.map (·.normalize)
  let mut exempted : Array (System.FilePath × Name) := #[]
  let mut listed : Array Name := #[]
  for exemption in sourceTokenExemptions do
    let moduleName := exemption.moduleName
    if isBlank exemption.reason then
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption for {moduleName} carries no reason"
    if listed.contains moduleName then
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption for {moduleName} is listed more than once"
      continue
    listed := listed.push moduleName
    let path := (Lean.modToFilePath projectRoot moduleName "lean").normalize
    let entryPath := (Lean.modToFilePath (projectRoot / "bin") moduleName "lean").normalize
    if entryPaths.contains path || entryPaths.contains entryPath then
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption for {moduleName} names an entry point under bin/, and no file under bin/ can be exempted"
    else if modulePaths.contains path then
      exempted := exempted.push (path, moduleName)
    else
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption names missing module {moduleName}"
  for scan in scans do
    match exempted.find? (·.1 == scan.source.normalize) with
    | some (_, moduleName) =>
        if scan.trustTokens.isEmpty then
          findings := findings.push
            m!"Whatwg source trust gate: stale source-token exemption for {moduleName}; its source contains no refused token"
    | none =>
        for hit in scan.trustTokens do
          findings := findings.push
            m!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` trust token at line {hit.line}, column {hit.column}"
  return findings

elab "#whatwg_streams_axiom_gate" : command => do
  let environment ← getEnv
  let sourceFile ← liftIO <| absoluteSourcePath (System.FilePath.mk (← getFileName))
  let some sourceDirectory := sourceFile.parent
    | throwError "Whatwg axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot

  -- 1. Module closure: every module source is imported by the test root.
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    (Lean.modToFilePath projectRoot moduleName "lean").normalize
  let unreachable := sources.modules.filter fun source =>
    source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize
  let closureFindings := unreachable.map fun source =>
    m!"Whatwg module-closure gate: {source.toString} is not reachable from the WhatwgTest audit root"
  unless (← reportFindings closureFindings) do
    return

  -- 2. The modifier pass, over every audited source. The scan also records the
  -- trust tokens pass 5 judges, so each source is tokenized once.
  let tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
  let mut scans : Array SourceScan := #[]
  for source in sources.modules ++ sources.entryPoints do
    scans := scans.push (← liftIO <| scanSource environment tokenTable source)
  unless (← reportFindings (modifierFindings scans)) do
    return

  -- 3. The environment pass, over every constant of an audited module.
  let declarations ←
    match auditedDeclarations environment with
    | .ok found => pure found
    | .error message => throwError message
  unless (← reportFindings (environmentFindings environment declarations)) do
    return

  -- 4. The axiom pass: R-11 everywhere, the strict ceiling under its prefixes.
  let repositoryCeilingText := ceilingText ", " repositoryCeiling
  let strictCeilingText := ceilingText " and " strictCeiling
  let (exceptionFindings, excepted) ← strictCeilingFindings environment declarations
  let mut axiomFindings := exceptionFindings
  let mut choiceReachers : Array AuditedDeclaration := #[]
  for declaration in declarations do
    let name := declaration.name
    let axioms ← collectAxioms name
    for axiomName in axioms do
      if isNativeAuxiliaryAxiom axiomName then
        axiomFindings := axiomFindings.push
          m!"Whatwg axiom gate: declaration {name} reaches forbidden axiom {axiomName} (native_decide auxiliary)"
      else if forbiddenAxioms.contains axiomName then
        axiomFindings := axiomFindings.push
          m!"Whatwg axiom gate: declaration {name} reaches forbidden axiom {axiomName}"
      else if !repositoryCeiling.contains axiomName then
        axiomFindings := axiomFindings.push
          m!"Whatwg axiom gate: declaration {name} reaches unexpected axiom {axiomName}; the ceiling is {repositoryCeilingText}"
    if axioms.contains ``Classical.choice then
      choiceReachers := choiceReachers.push declaration
      if let some strictPrefix := strictPrefixOf? declaration.moduleName then
        if !excepted.contains name then
          axiomFindings := axiomFindings.push
            m!"Whatwg axiom gate: declaration {name} reaches Classical.choice under the strict ceiling of {strictPrefix}, which admits {strictCeilingText} only, and no exact exception names it"
  unless (← reportFindings axiomFindings) do
    return

  -- 5. The trust-token pass and its exemptions.
  unless (← reportFindings (trustTokenFindings projectRoot sources scans)) do
    return

  -- The summary: one line, counts only, in the template of contract section 7.
  let inTree (tree : Name) (found : Array AuditedDeclaration) : Nat :=
    (found.filter (·.tree == tree)).size
  let sourceCount := sources.modules.size + sources.entryPoints.size
  let whatwgReached := inTree `Whatwg choiceReachers
  let whatwgTotal := inTree `Whatwg declarations
  let testReached := inTree `WhatwgTest choiceReachers
  let testTotal := inTree `WhatwgTest declarations
  let gatesReached := inTree `Gates choiceReachers
  let gatesTotal := inTree `Gates declarations
  let prefixCount := strictCeilingPrefixes.length
  let exceptionCount :=
    strictCeilingExceptions.length + privateStrictCeilingExceptions.length
  let exemptionCount := sourceTokenExemptions.length
  logInfo m!"Whatwg module and axiom gate: checked {sourceCount} source files and {declarations.size} declarations; Classical.choice is reached by {whatwgReached} of {whatwgTotal} declarations in Whatwg, {testReached} of {testTotal} in WhatwgTest and {gatesReached} of {gatesTotal} in Gates; strict ceiling propext and Quot.sound over {prefixCount} module prefix(es) with {exceptionCount} exact exception(s); {exemptionCount} source-token exemption(s)"

end WhatwgTest.Audit
