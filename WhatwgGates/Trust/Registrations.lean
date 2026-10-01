import WhatwgGates.Trust.Tokens

/-!
# Gates.Trust.Registrations

The metaprogramming-module rule of the trust gate, rule 1 of addendum V2c of
`test/contracts/trust-gate-hardening.contract.md` (V2c.2), in its environment
half, and the checks of the list `metaprogrammingModules` itself: an audited
module that registers a token, parser, syntax category, macro, elaborator or
initializer is refused unless it is listed, and every list entry must name a
module source that spells a metaprogramming keyword or registers something,
carry a reason, occur once, and name no entry point under `whatwgbin/`. The
token half of the rule is `keywordAndShapeFindings` of
`WhatwgGates/Trust/Tokens.lean`.

The registrations are read from each audited module's entries in the parser
extension, the keyed declaration attributes and the `init` attributes, through
`getModuleEntries` and `getModuleIREntries` of extensions the reading process
registers. An import fills those entries in whether or not it loads the
extensions, so an environment imported with `loadExts := false` yields the same
registrations; no extension's state is read. The readers name attributes
declared across `Lean.Elab`, `Lean.PrettyPrinter` and `Lean.Compiler`, which is
why the library imports `Lean` whole.
-/

namespace Gates.Trust

open Lean

/-- One registration an audited module's environment entries record (rule 1 of
addendum V2c, environment half). -/
structure Registration where
  /-- The module whose entries record the registration. -/
  moduleName : Name
  /-- What it registers, with its article, as the diagnostic prints it. -/
  kind : String
  /-- What exactly it registers. -/
  detail : String
  /-- The registered declaration, when the entry names one. -/
  declaration? : Option Name := none

/-- The (key, declaration) entries one module records in a keyed declaration
attribute, global and scoped alike. -/
def keyedEntriesOf {γ : Type} (keyed : KeyedDeclsAttribute γ)
    (environment : Environment) (index : Nat) : Array (Name × Name) :=
  (keyed.ext.ext.getModuleEntries environment index).map fun
    | .global entry => (entry.key, entry.declName)
    | .scoped _ entry => (entry.key, entry.declName)

/-- The keyed declaration attributes whose entries register a macro or an
elaborator, with the kind a refusal names. Every elaboration hook the toolchain
keys by syntax kind counts as an elaborator: command, term, tactic and
`do`-element elaborators, and the hooks of `inductive`, quotation prechecks,
`try?`, `grind` and its simproc language; so do the pretty-printing hooks
(delaborators, unexpanders, formatters and parenthesizers), which run a
metaprogram whenever a later module prints. -/
def keyedRegistrationReaders :
    List (String × (Environment → Nat → Array (Name × Name))) :=
  [ ("a macro", keyedEntriesOf Elab.macroAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Command.commandElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Term.termElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.tacticElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Do.doElemElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Do.controlInfoElemAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Command.inductiveElabAttr)
  , ("an elaborator", keyedEntriesOf Elab.Term.Quotation.precheckAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Try.tryTacticElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.grindTacElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.symSimprocElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.symDSimprocElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.symDischargerElabAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.Delaborator.delabAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.Delaborator.appUnexpanderAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.formatterAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.parenthesizerAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.categoryParenthesizerAttribute)
  ]

/-- Every registration one module's entries record: the parser extension's
token, syntax kind, category and parser entries, global and scoped; every
keyed declaration attribute of `keyedRegistrationReaders`; and the `init` and
`builtin_init` attributes, which `initialize`, `builtin_initialize` and the
`register_…` commands produce, read from the module's `.olean` and `.ir`
entries alike. Every read is `getModuleEntries` or `getModuleIREntries` of an
extension the reading process registers, whose imported entries an import fills
in whether or not it loads the extensions, so a process that imports with
`loadExts := false` reads the same registrations. -/
def registrationsOf (environment : Environment) (index : Nat) (moduleName : Name) :
    Array Registration := Id.run do
  let mut found : Array Registration := #[]
  for entry in Parser.parserExtension.ext.getModuleEntries environment index do
    let parserEntry := match entry with
      | .global parserEntry => parserEntry
      | .scoped _ parserEntry => parserEntry
    match parserEntry with
    | .token token =>
        found := found.push { moduleName, kind := "a token", detail := s!"the token `{token}`" }
    | .kind kind =>
        found := found.push { moduleName, kind := "a parser", detail := s!"the syntax kind {kind}" }
    | .category category declaration _ =>
        found := found.push
          { moduleName, kind := "a syntax category", detail := s!"the category {category}",
            declaration? := some declaration }
    | .parser category declaration _ =>
        found := found.push
          { moduleName, kind := "a parser",
            detail := s!"the parser {declaration} of category {category}",
            declaration? := some declaration }
  for (kind, reader) in keyedRegistrationReaders do
    for (key, declaration) in reader environment index do
      found := found.push
        { moduleName, kind, detail := s!"the declaration {declaration} for {key}",
          declaration? := some declaration }
  for initAttribute in [regularInitAttr, builtinInitAttr] do
    let entries := initAttribute.ext.getModuleEntries environment index ++
      initAttribute.ext.getModuleIREntries environment index
    for (declaration, _) in entries do
      found := found.push
        { moduleName, kind := "an initializer", detail := s!"the declaration {declaration}",
          declaration? := some declaration }
  -- An `.ir` entry repeats its `.olean` entry when both are loaded: keep one.
  let mut unique : Array Registration := #[]
  for registration in found do
    unless unique.any (fun seen => seen.kind == registration.kind &&
        seen.detail == registration.detail) do
      unique := unique.push registration
  return unique

/-- Every registration of every audited module. -/
def auditedRegistrations (config : Config) (environment : Environment) :
    Array Registration := Id.run do
  let mut found : Array Registration := #[]
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if (treeOf? config moduleName).isSome then
      found := found ++ registrationsOf environment index moduleName
  return found

/-- The modules `metaprogrammingModules` lists. -/
def listedMetaprogrammingModules (config : Config) : NameSet :=
  config.metaprogrammingModules.foldl (init := {}) fun listed entry => listed.insert entry.moduleName

/-- Pass 3, the environment half of rule 1 (addendum V2c.2): a registration is
attributed to the module whose entries record it and, when the registered
declaration belongs to another audited module, to that module as well; either
one that is not listed is refused. -/
def registrationFindings (config : Config) (environment : Environment)
    (registrations : Array Registration) : Array String := Id.run do
  let listed := listedMetaprogrammingModules config
  let mut findings : Array String := #[]
  for registration in registrations do
    unless listed.contains registration.moduleName do
      findings := findings.push
        s!"Whatwg trust gate: module {registration.moduleName} registers {registration.kind} but is not a listed metaprogramming module: {registration.detail}"
    if let some declaration := registration.declaration? then
      if let some owner := moduleOf? environment declaration then
        if owner != registration.moduleName && (treeOf? config owner).isSome &&
            !listed.contains owner then
          findings := findings.push
            s!"Whatwg trust gate: module {owner} registers {registration.kind} but is not a listed metaprogramming module: {registration.detail}, whose declaration it owns, registered by module {registration.moduleName}"
  return findings

/-- Pass 5, the checks of `metaprogrammingModules` itself (addendum V2c.2):
an entry with a blank reason, one listed twice, one that names an entry point
under `whatwgbin/`, one that names no audited module source, and one whose
source spells no metaprogramming keyword while its module registers nothing. -/
def metaprogrammingListFindings (config : Config) (environment : Environment)
    (projectRoot : System.FilePath) (sources : AuditedSources) (scans : Array SourceScan)
    (registrations : Array Registration) : Array String := Id.run do
  let mut findings : Array String := #[]
  let modulePaths := sources.modules.map pathKey
  let entryPaths := sources.entryPoints.map pathKey
  let mut listed : Array Name := #[]
  for entry in config.metaprogrammingModules do
    let moduleName := entry.moduleName
    if isBlank entry.reason then
      findings := findings.push
        s!"Whatwg trust gate: metaprogramming-module entry for {moduleName} carries no reason"
    if listed.contains moduleName then
      findings := findings.push
        s!"Whatwg trust gate: metaprogramming-module entry for {moduleName} is listed more than once"
      continue
    listed := listed.push moduleName
    let path := pathKey (Lean.modToFilePath projectRoot moduleName "lean")
    let entryPath := pathKey (Lean.modToFilePath (projectRoot / "whatwgbin") moduleName "lean")
    if entryPaths.contains path || entryPaths.contains entryPath then
      findings := findings.push
        s!"Whatwg trust gate: metaprogramming-module entry for {moduleName} names an entry point under whatwgbin/, which cannot be a metaprogramming module"
    else if !modulePaths.contains path then
      findings := findings.push
        s!"Whatwg trust gate: metaprogramming-module entry names missing module {moduleName}"
    else
      let spellsKeyword := scans.any fun scan =>
        pathKey scan.source == path && !scan.metaprogrammingKeywords.isEmpty
      let registers := registrations.any fun registration =>
        registration.moduleName == moduleName ||
          (registration.declaration?.bind (moduleOf? environment ·)) == some moduleName
      unless spellsKeyword || registers do
        findings := findings.push
          s!"Whatwg trust gate: stale metaprogramming-module entry for {moduleName}; its source declares no syntax, macro or elaborator and registers nothing"
  return findings

end Gates.Trust
