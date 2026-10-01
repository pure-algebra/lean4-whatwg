import Lean
import Lean.Util.CollectAxioms
import Whatwg
import WhatwgGates
import WhatwgGates.TrustConfig
import WhatwgGates.Trust.Tokens

/-!
# Whatwg trust and axiom gate

`#whatwg_streams_axiom_gate`, the last command of the test root `WhatwgTest.lean`,
decides where trust enters the repository. It reads three things: every authored
source under `Whatwg/`, `WhatwgTest/`, `WhatwgGates/` and `whatwgbin/` with the
three roots; every constant and every registration of every audited module in
the compiled environment, authored, private, auxiliary and Lean-generated alike;
and the final token table. Its behaviour is frozen by
`test/contracts/trust-gate-hardening.contract.md` (rulings R-V1 and R-V2, R-V6 in
addendum V2b, R-V10 in addendum V2c) and falsified by
`lake exe whatwg_trustselftest`.

## Passes, in order

The gate runs its passes in the order of the contract's section 3, numbered as
there, with the checks addendum V2c.1 slots into it. Every pass runs and logs
every finding it has, one error per finding, in that order; the summary line is
logged only when no pass has a finding. The contract's section 3 admits a gate
that collects every finding, and this one must: six older plants (V2-T03,
V2-T04, V2-T08, V2-T09, V2-T10 and V2b-T10) declare a `macro` or an `elab` in a
module that is not a metaprogramming module, so rule 1 refuses each at the
environment pass, and a gate that stopped there would never print the
trust-token fragment each of those rows expects. The order still decides which
message comes first.

0. *Root pass* (V2c rule 4, before step 1). The root holds only `import` lines,
   comments, documentation and `#whatwg_streams_axiom_gate`, which is its last
   command, and the root module has declared no constant when the gate runs.
   The gate runs only in the root.
1. *Module closure.* Every module source is imported by the test root, and
   (V2c rule 5) every environment module under an audited prefix maps, by exact
   case-sensitive path, to exactly one scanned source. A file whose extension is
   `lean` in any case is scanned, so a `.LEAN` file that a case-insensitive host
   builds is reported in both directions, never skipped. `whatwgbin/` is
   excluded: its files are executable roots no audit root imports.
2. *Modifier pass.* An authored `unsafe` or `partial` keyword in code, in any
   audited source, `whatwgbin/` included, is refused; so is a source the
   tokenizer cannot read to its end. After it, as a pass of its own,
   *token-table hygiene* (V2c rule 2): every token of the final table, scoped
   entries included, that neither the `lean` binary nor an `Init` module
   declares must be inert (tests T1 to T3 of addendum V2c.3), so that no token
   hides a refused word from the source passes, whoever declared it.
3. *Environment pass.* Over every constant of an audited module, apart from a
   generated safe recursor: an `unsafe` or `partial` constant, a declared
   axiom (a native-evaluation auxiliary named as such), an `@[extern]` or
   `@[implemented_by]` constant, and an `opaque` whose value Lean synthesised.
   Then (V2c rule 1, environment half) every registration an audited module's
   entries record: a token, parser, syntax category, macro, elaborator or
   initializer, refused unless both the recording module and, when it is
   audited, the module that owns the registered declaration are listed in
   `metaprogrammingModules`.
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
   entry in `sourceTokenExemptions`; every entry is checked for need. Then
   (V2c rule 1, token half) a metaprogramming keyword in code outside a listed
   module, the five checks of `metaprogrammingModules` itself, and (V2c rule 3)
   every `(config := …)` whose value is not a literal brace group without
   `with` closed by `)`.

A successful run logs one summary line with the per-tree counts of
declarations that reach `Classical.choice`; addendum V2c adds no field.

## The post-command check

Every pass above runs inside the elaborator of `#whatwg_streams_axiom_gate`,
so a module that replaces that command (a `macro_rules` or an `@[command_elab]`
for its syntax, or another parser for its token) would silence them all. When
this module is imported it therefore registers, with `initialize`, a linter
that runs after each command of the root and a module linter that runs after
the root's last command (addendum V2c.5). Neither is reached through the gate
command's syntax, and both act only in the root, which they recognise by its
file: the file being elaborated must be `WhatwgTest.lean` in the directory that
holds `Whatwg.lean`, compared exactly, so a plant or any other module that
imports this one is never treated as the root. After a root command of the
gate's syntax kind the linter checks that no macro and no elaborator other than
this module's is registered for that kind, so that this module's elaborator ran
it; after the root's last command the module linter checks that some top-level
command of the root was parsed as the gate command at all, which a missing
command, another parser for its token, or a wrapper such as
`#guard_msgs (drop all) in` (which would discard its verdict) breaks. When
either check fails it logs "the gate command of WhatwgTest.lean did not run the
gate" and runs every pass itself, so rule 1 names the module that replaced the
command. The check reads state that code running in the same process could
change: an initializer, a command of the root, or a replacing elaborator that
removes the linters or edits what they read is refused by rule 1 or the root
pass only when a pass runs, and otherwise by `lake exe whatwg_trustselftest`,
whose rejection rows would then all be accepted (contract V2c.7).

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
spells every refused word and every metaprogramming keyword it does not use as
a string literal and every axiom as a name literal, so it needs no exemption of
its own; it is a listed metaprogramming module because it declares the gate
command, its elaborator and the post-command check.

`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for the source passes, and token-table hygiene bounds what a later
module's syntax can do to that tokenization; the environment pass independently
confirms what the compiled constants and registrations are.

Sections 13, V2b.6 and V2c.7 of the contract state what a green gate does not
mean: among others, a name built by metaprogramming, an option set outside the
source, a dependency's syntax and macros, the toolchain's own non-inert base
tokens, and code that runs before the post-command check (an initializer, or a
command in the root) and removes it are invisible to these passes, and
`whatwgbin/` is read by the source passes only.

This gate began as a port of lean4-effect4's `Effect4Test/Audit/AxiomGate.lean`;
the environment pass follows that gate at `0f16828a`, as R-V2 directs.
-/

open Lean

namespace WhatwgTest.Audit

/-! ## The gate library

The audited trees, both ceilings, the strict prefixes and the three anchored
lists are this repository's data, held by `Gates.TrustConfig.config` in
`WhatwgGates/TrustConfig.lean`; the passes moved so far live in the gate library
`WhatwgGates/Trust/` (addendum V2e.3, ruling R-W7(a)), and every pass that reads
the data takes it as an argument, `config : Config`. -/

open Gates.Trust

/-! ## Source tokens -/

/-- The one token of the gate command. -/
private def gateCommandToken : String :=
  "#whatwg_streams_axiom_gate"

/-! ## Token-table hygiene -/

/-- The whole-name words of the inert test T3: every refused word as printed and
the two modifier keywords. -/
private def inertWholeWords : List String :=
  refusedWords.map (·.printed) ++ modifierWords

/-- The last-component words of the inert test T3: the short names of the
forbidden axioms, of `sorryAx` and of the two kernel-evaluation hooks. -/
private def inertLastComponents : List String :=
  refusedWords.filterMap (·.lastComponent?)

/-- The identifier read from index `start`, as the inert test T3 reads it:
components joined by `.` when the character after the dot may begin one, up to
a character that may not continue it or the end. Returns the spelling, the index
after it, and whether exactly one `.` follows it at the very end. -/
private def readIdentifier (characters : Array Char) (start : Nat) : String × Nat × Bool :=
  Id.run do
  let mut index := start
  let mut spelling := ""
  for _ in [0:characters.size + 1] do
    match characters[index]? with
    | none => break
    | some character =>
        if spelling.isEmpty || spelling.back == '.' then
          if isIdFirst character then
            spelling := spelling.push character
            index := index + 1
          else
            break
        else if isIdRest character then
          spelling := spelling.push character
          index := index + 1
        else if character == '.' && ((characters[index + 1]?).map isIdFirst).getD false then
          spelling := spelling.push '.'
          index := index + 1
        else
          break
  let trailingDot := index + 1 == characters.size && characters[index]? == some '.'
  return (spelling, index, trailingDot)

/-- The fragments test T1 refuses inside a token, each with how a reason names it. -/
private def inertForbiddenFragments : List (String × String) :=
  [(" ", "a space"), ("\t", "a tab"), ("\r", "a carriage return"), ("\n", "a line feed"),
    ("\"", "`\"`"), ("«", "`«`"), ("»", "`»`"), ("--", "`--`"), ("/-", "`/-`"), ("-/", "`-/`")]

/-- Why a token fails the inert test of addendum V2c.3, empty when it is inert.
`splitters` are the tokens of the table that contain a character that cannot
continue an identifier: an identifier may start right after one of them. -/
private def inertFailures (splitters : Array String) (token : String) : Array String := Id.run do
  let characters := token.toList.toArray
  let continues (index : Nat) : Bool := ((characters[index]?).map isIdRest).getD false
  let mut reasons : Array String := #[]
  -- T1: whitespace, quotes, guillemets and comment delimiters.
  for (fragment, described) in inertForbiddenFragments do
    if (token.splitOn fragment).length > 1 then
      reasons := reasons.push s!"T1, it contains {described}"
  -- T2: a trailing `-` or `/`, and a character-literal opener.
  if token.endsWith "-" then
    reasons := reasons.push "T2, it ends in `-`"
  if token.endsWith "/" then
    reasons := reasons.push "T2, it ends in `/`"
  for index in [0:characters.size] do
    if characters[index]? == some '\'' then
      let opens := match index with
        | 0 => true
        | previous + 1 => !continues previous
      if opens then
        reasons := reasons.push s!"T2, the `'` at index {index} opens a character literal"
  -- T3, with T2's raw-string opener, at every identifier start.
  for index in [0:characters.size] do
    let some character := characters[index]? | continue
    unless isIdFirst character do continue
    let before := String.ofList (characters.toList.take index)
    let starts := match index with
      | 0 => true
      | previous + 1 =>
          !continues previous || splitters.any fun splitter => before.endsWith splitter
    unless starts do continue
    let (spelling, stop, trailingDot) := readIdentifier characters index
    if spelling.isEmpty then continue
    if spelling == "r" &&
        (stop == characters.size || characters[stop]? == some '#' || characters[stop]? == some '"') then
      reasons := reasons.push s!"T2, the identifier `r` at index {index} opens a raw string literal"
    if stop == characters.size || trailingDot then
      let read := if trailingDot then spelling ++ "." else spelling
      for word in inertWholeWords do
        if word.startsWith read then
          reasons := reasons.push
            s!"T3, the identifier `{read}` at index {index} reaches the end of the token and begins the refused word `{word}`"
      let lastComponent := ((read.splitOn ".").getLast?).getD read
      unless lastComponent.isEmpty do
        for component in inertLastComponents do
          if component.startsWith lastComponent then
            reasons := reasons.push
              s!"T3, the last component `{lastComponent}` of the identifier at index {index} reaches the end of the token and begins the refused component `{component}`"
    else
      if inertWholeWords.contains spelling then
        reasons := reasons.push
          s!"T3, the identifier `{spelling}` at index {index} is the refused word `{spelling}`"
      let lastComponent := ((spelling.splitOn ".").getLast?).getD spelling
      if inertLastComponents.contains lastComponent then
        reasons := reasons.push
          s!"T3, the identifier `{spelling}` at index {index} ends in the refused component `{lastComponent}`"
  return reasons

/-- The tokens of the final table, scoped entries included, that neither the
`lean` binary nor an `Init` module declares, each with the modules whose parser
entries declare it. `finalTable` is the final token table and `scopedTokens`
every scoped `.token` entry of the environment, both read by the host. The
per-module parser entries are read with `getModuleEntries`, which an import
fills in whether or not it loads the extensions. -/
private def nonBaseTokens (environment : Environment) (finalTable : Parser.TokenTable)
    (scopedTokens : Array String) : IO (Array String × Array (String × Array Name)) := do
  let builtinTable ← Parser.builtinTokenTable.get
  let mut initDeclared : Std.HashSet String := {}
  let mut declaredBy : Std.HashMap String (Array Name) := {}
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    for entry in Parser.parserExtension.ext.getModuleEntries environment index do
      let token? : Option String := match entry with
        | .global (.token token) => some token
        | .scoped _ (.token token) => some token
        | _ => none
      if let some token := token? then
        declaredBy := declaredBy.insert token ((declaredBy.getD token #[]).push moduleName)
        if (`Init).isPrefixOf moduleName then
          initDeclared := initDeclared.insert token
  let mut table : Std.HashSet String := {}
  for token in finalTable.values do
    table := table.insert token
  for token in scopedTokens do
    table := table.insert token
  let tokens := table.toArray.qsort (· < ·)
  let nonBase := tokens.filter fun token =>
    (builtinTable.find? token).isNone && !initDeclared.contains token
  return (tokens, nonBase.map fun token => (token, declaredBy.getD token #[]))

/-! ## Registrations -/

/-- One registration an audited module's environment entries record (rule 1 of
addendum V2c, environment half). -/
private structure Registration where
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
private def keyedEntriesOf {γ : Type} (keyed : KeyedDeclsAttribute γ)
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
private def keyedRegistrationReaders :
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
private def registrationsOf (environment : Environment) (index : Nat) (moduleName : Name) :
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
private def auditedRegistrations (config : Config) (environment : Environment) :
    Array Registration := Id.run do
  let mut found : Array Registration := #[]
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if (treeOf? config moduleName).isSome then
      found := found ++ registrationsOf environment index moduleName
  return found

/-! ## The passes -/

/-- One token of the root as the root pass reads it. -/
private inductive RootTag where
  | importKeyword
  | identifier
  | gateCommand
  | other
  deriving BEq, Inhabited

/-- How a diagnostic shows one token: an atom's text, an identifier's spelling,
or the text of a literal. -/
private def tokenText : Syntax → String
  | .atom _ text => text
  | .ident _ raw _ _ => raw.toString
  | .node _ kind arguments =>
      match (arguments[0]? : Option Syntax) with
      | some (Syntax.atom _ text) => text
      | _ => kind.toString
  | .missing => "<missing>"

private def rootTagOf (token : Syntax) : RootTag :=
  if token.isToken "import" then .importKeyword
  else if token.isToken gateCommandToken then .gateCommand
  else if token.isIdent then .identifier
  else .other

/-- Pass 0 over the root's tokens of code (rule 4 of addendum V2c): `import` and
a module name, any number of times, then the gate command and nothing after it. -/
private def rootShapeFindings (tokens : Array (RootTag × String × SourcePosition)) :
    Array String := Id.run do
  let tagAt (index : Nat) : RootTag := (tokens[index]?.map (·.1)).getD .other
  let mut index := 0
  for _ in [0:tokens.size] do
    if tagAt index == .importKeyword && tagAt (index + 1) == .identifier then
      index := index + 2
    else
      break
  let gateIndex := (tokens.findIdx? (·.1 == RootTag.gateCommand)).getD tokens.size
  let mut findings : Array String := #[]
  if index < gateIndex then
    if let some (_, text, position) := tokens[index]? then
      findings := findings.push
        s!"Whatwg axiom gate: the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate: `{text}` at line {position.line}, column {position.column}"
  if gateIndex == tokens.size then
    findings := findings.push
      s!"Whatwg axiom gate: #whatwg_streams_axiom_gate is not the last command of the root: the root has no #whatwg_streams_axiom_gate command"
  else if let some (_, text, position) := tokens[gateIndex + 1]? then
    findings := findings.push
      s!"Whatwg axiom gate: #whatwg_streams_axiom_gate is not the last command of the root: `{text}` follows it at line {position.line}, column {position.column}"
  return findings

/-- Pass 0, the root pass (rule 4 of addendum V2c): the gate runs in the root;
the root's source, the text being elaborated, holds only imports, comments,
documentation and the gate command as its last command; and the root module has
declared no constant. `rootConstants` are the constants the root module has
declared when the gate runs, which only a host that elaborates the root can
read; a host that does not passes none. -/
private def rootFindings (environment : Environment) (tokenTable : Parser.TokenTable)
    (projectRoot sourceFile : System.FilePath) (sourceText : String)
    (rootConstants : Array Name) : Array String :=
  Id.run do
  let mut findings : Array String := #[]
  let rootFile := projectRoot / "WhatwgTest.lean"
  if pathKey sourceFile != pathKey rootFile then
    findings := findings.push
      s!"Whatwg axiom gate: #whatwg_streams_axiom_gate runs in {sourceFile}, which is not the root {rootFile}; the gate runs only as the root's last command"
  let (tokens, failure?) := foldCodeTokens environment tokenTable sourceFile.toString sourceText
    (#[] : Array (RootTag × String × SourcePosition))
    fun tokens token position => tokens.push (rootTagOf token, tokenText token, position)
  if let some failure := failure? then
    findings := findings.push failure
  findings := findings ++ rootShapeFindings tokens
  let declared := rootConstants.qsort fun left right => left.toString < right.toString
  for name in declared do
    findings := findings.push
      s!"Whatwg axiom gate: the root module WhatwgTest has declared a constant when the gate runs; the root must declare none, and it declares {name}"
  return findings

/-- The pass after pass 2, token-table hygiene (rule 2 of addendum V2c): every
non-base token of the final table is inert. -/
private def tokenTableFindings (tokens : Array String) (nonBase : Array (String × Array Name)) :
    Array String :=
  let splitters := tokens.filter fun token => token.any fun character => !isIdRest character
  nonBase.filterMap fun (token, declaredBy) =>
    let reasons := inertFailures splitters token
    if reasons.isEmpty then
      none
    else
      let declarers :=
        if declaredBy.isEmpty then "no module's parser entries; the module header adds it"
        else ", ".intercalate (declaredBy.toList.map toString)
      some s!"Whatwg source trust gate: token `{token}` of the final token table is not inert: {"; ".intercalate reasons.toList}; declared by {declarers}"

/-- The modules `metaprogrammingModules` lists. -/
private def listedMetaprogrammingModules (config : Config) : NameSet :=
  config.metaprogrammingModules.foldl (init := {}) fun listed entry => listed.insert entry.moduleName

/-- Pass 3, the environment half of rule 1 (addendum V2c.2): a registration is
attributed to the module whose entries record it and, when the registered
declaration belongs to another audited module, to that module as well; either
one that is not listed is refused. -/
private def registrationFindings (config : Config) (environment : Environment)
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
private def metaprogrammingListFindings (config : Config) (environment : Environment)
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

/-! ## The host and the run -/

/-- What only the gate's host can read, handed to the passes as data: the
in-tree command reads each from its elaboration state, and an executable over
built files reads its equivalent from their raw entries. -/
private structure HostReads where
  /-- The final token table every source pass tokenizes with. -/
  tokenTable : Parser.TokenTable
  /-- Every scoped `.token` entry of the environment, which token-table hygiene
  adds to the final table (addendum V2c.3). -/
  scopedTokens : Array String
  /-- The constants the root module has declared when the gate runs; none for a
  host that does not elaborate the root. -/
  rootConstants : Array Name

/-- What the gate's host does for the passes. -/
private structure Host (m : Type → Type) where
  /-- The axioms one constant reaches. -/
  axiomsOf : Name → m (Array Name)
  /-- Print every finding of one pass, in order; called once per pass, also when
  the pass has none. -/
  report : Array String → m Unit

/-- Hand every finding of one pass to the host, and say whether there was none. -/
private def reportFindings {m : Type → Type} [Monad m] (host : Host m)
    (findings : Array String) : ExceptT String m Bool := do
  host.report findings
  return findings.isEmpty

/-- Every pass, in order, over the project that holds `sourceFile`, the file the
gate runs for, whose text is `sourceText` (contract section 3, as addendum V2c.1
extends it). Each pass hands its findings to `host.report`; the summary is
returned only when no pass has a finding. The error is a failure that stops the
run: a source file with no parent directory, or an environment whose module
tables disagree. -/
private def runPasses {m : Type → Type} [Monad m] [MonadLiftT IO m] (config : Config)
    (host : Host m) (environment : Environment) (reads : HostReads)
    (sourceFile : System.FilePath) (sourceText : String) :
    ExceptT String m (Option Summary) := do
  let some sourceDirectory := sourceFile.parent
    | throwThe String "Whatwg axiom gate: source file has no parent directory"
  let projectRoot ← findProjectRoot sourceDirectory
  let sources ← auditedSources projectRoot
  let tokenTable := reads.tokenTable
  let mut clean := true

  -- 0. The root pass (addendum V2c, rule 4).
  clean := (← reportFindings host
    (rootFindings environment tokenTable projectRoot sourceFile sourceText
      reads.rootConstants)) && clean

  -- 1. Module closure, in both directions (rule 5 is the reverse one).
  clean := (← reportFindings host
    (closureFindings config environment projectRoot sourceFile sources)) && clean

  -- 2. The modifier pass, over every audited source. The scan also records what
  -- pass 5 judges, so each source is tokenized once.
  let mut scans : Array SourceScan := #[]
  for source in sources.modules ++ sources.entryPoints do
    scans := scans.push (← scanSource environment tokenTable source)
  clean := (← reportFindings host (modifierFindings scans)) && clean

  -- After pass 2, token-table hygiene (rule 2).
  let (tableTokens, nonBase) ← nonBaseTokens environment tokenTable reads.scopedTokens
  clean := (← reportFindings host (tokenTableFindings tableTokens nonBase)) && clean

  -- 3. The environment pass, over every constant of an audited module, then the
  -- environment half of rule 1 over every registration of one.
  let declarations ←
    match auditedDeclarations config environment with
    | .ok found => pure found
    | .error message => throwThe String message
  let registrations := auditedRegistrations config environment
  clean := (← reportFindings host
    (environmentFindings environment declarations ++
      registrationFindings config environment registrations)) && clean

  -- 4. The axiom pass: R-11 everywhere, the strict ceiling under its prefixes.
  let (axiomFindings, choiceReachers) ←
    (axiomPassFindings config host.axiomsOf environment declarations : m _)
  clean := (← reportFindings host axiomFindings) && clean

  -- 5. The trust-token pass and its exemptions, then the token half of rule 1
  -- with the checks of its list, and rule 3.
  clean := (← reportFindings host
    (trustTokenFindings config projectRoot sources scans ++
      metaprogrammingListFindings config environment projectRoot sources scans registrations ++
      keywordAndShapeFindings config projectRoot sources scans)) && clean

  unless clean do
    return none

  -- The summary: counts only, in the template of contract section 7.
  let inTree (tree : Name) (found : Array AuditedDeclaration) : Nat :=
    (found.filter (·.tree == tree)).size
  return some
    { sourceCount := sources.modules.size + sources.entryPoints.size
      declarationCount := declarations.size
      whatwgReached := inTree `Whatwg choiceReachers
      whatwgTotal := inTree `Whatwg declarations
      testReached := inTree `WhatwgTest choiceReachers
      testTotal := inTree `WhatwgTest declarations
      gatesReached := inTree `WhatwgGates choiceReachers -- R-V3(c), 2026-10-01
      gatesTotal := inTree `WhatwgGates declarations -- R-V3(c), 2026-10-01
      prefixCount := config.strictCeilingPrefixes.length
      exceptionCount :=
        config.strictCeilingExceptions.length + config.privateStrictCeilingExceptions.length
      exemptionCount := config.sourceTokenExemptions.length }

/-! ## The in-tree host

What only an elaborating process can read, this module reads and hands to the
passes: the final token table and the scoped tokens from the parser extension's
loaded state, the root module's own constants, and each constant's axioms
through `Lean.collectAxioms`, which reads the loaded per-module axiom tables. -/

open Elab Command

/-- Every scoped `.token` entry the parser extension's loaded state holds: the
tokens token-table hygiene adds to the final table (addendum V2c.3). -/
private def scopedTokenEntries (environment : Environment) : Array String := Id.run do
  let mut tokens : Array String := #[]
  for (_, entries) in (Parser.parserExtension.ext.getState environment).scopedEntries.map.toList do
    for entry in entries.toArray do
      if let .token token := entry then
        tokens := tokens.push token
  return tokens

/-- Every pass, in order, over the project that holds `sourceFile`, the file the
gate command runs in, whose elaborated text is `sourceText`. Each pass logs every
finding as its own error; the summary line is logged only when no pass has one. -/
private def runGate (sourceFile : System.FilePath) (sourceText : String) : CommandElabM Unit := do
  let environment ← getEnv
  let reads : HostReads :=
    { tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
      scopedTokens := scopedTokenEntries environment
      rootConstants := (environment.constants.map₂.toList.map (·.1)).toArray }
  let host : Host CommandElabM :=
    { axiomsOf := fun declaration => collectAxioms declaration
      report := fun findings => do
        for finding in findings do
          logError m!"{finding}" }
  match ← (runPasses Gates.TrustConfig.config host environment reads sourceFile sourceText).run with
  | .ok (some summary) => logInfo m!"{summary.line}"
  | .ok none => pure ()
  | .error message => throwError message

/-! ## The gate command and the post-command check -/

/-- The gate command, run as the last command of the root `WhatwgTest.lean`. -/
syntax "#whatwg_streams_axiom_gate" : command

/-- The syntax kind of the gate command. -/
private def gateKind : Name :=
  ``«command#whatwg_streams_axiom_gate»

/-- The gate's own elaborator: every pass, over the file the command runs in. -/
@[command_elab «command#whatwg_streams_axiom_gate»]
private def elabAxiomGate : CommandElab := fun _ => do
  let sourceFile ← liftIO <| absoluteSourcePath (System.FilePath.mk (← getFileName))
  runGate sourceFile (← getFileMap).source

/-- The file being elaborated, when it is the root: `WhatwgTest.lean` in the
directory that holds `Whatwg.lean`, compared exactly. Every other module that
imports this one, a plant included, is not the root, so the post-command check
does nothing there. -/
private def rootFile? : CommandElabM (Option System.FilePath) := do
  let sourceFile ← liftIO <| absoluteSourcePath (System.FilePath.mk (← getFileName))
  unless sourceFile.fileName == some "WhatwgTest.lean" do
    return none
  let some sourceDirectory := sourceFile.parent | return none
  try
    let projectRoot ← liftIO <| findProjectRoot sourceDirectory
    if pathKey (projectRoot / "WhatwgTest.lean") == pathKey sourceFile then
      return some sourceFile
    return none
  catch _ =>
    return none

/-- Why the gate's own elaborator did not run a command of the gate's syntax
kind, or `none` when it did: no macro is registered for that kind, and the only
command elaborator registered for it is `elabAxiomGate`. -/
private def gateReplacement? (environment : Environment) : Option String :=
  let macros := (Elab.macroAttribute.getEntries environment gateKind).map (·.declName)
  let elaborators :=
    (Elab.Command.commandElabAttribute.getEntries environment gateKind).map (·.declName)
  let owner (declaration : Name) : String :=
    match moduleOf? environment declaration with
    | some moduleName => s!"{declaration} of module {moduleName}"
    | none => s!"{declaration} of the root"
  if !macros.isEmpty then
    some s!"a macro is registered for it: {", ".intercalate (macros.map owner)}"
  else if elaborators != [``elabAxiomGate] then
    some s!"its command elaborators are {", ".intercalate (elaborators.map owner)}, not {``elabAxiomGate} alone"
  else
    none

/-- Log that the gate command of the root did not run the gate, then run every
pass, so that rule 1 names the module that replaced the command. -/
private def runReplacedGate (rootFile : System.FilePath) (reason : String) :
    CommandElabM Unit := do
  logError m!"Whatwg axiom gate: the gate command of WhatwgTest.lean did not run the gate; {reason}; the post-command check runs every pass instead"
  runGate rootFile (← getFileMap).source

/-- The linter half of the post-command check (addendum V2c.5): after each
command of the root, and for a command of the gate's syntax kind, check that
the gate's own elaborator ran it. -/
private def checkRootGateCommand (command : Syntax) : CommandElabM Unit := do
  unless command.getKind == gateKind do return
  let some rootFile ← rootFile? | return
  if let some reason := gateReplacement? (← getEnv) then
    withRef command <| runReplacedGate rootFile reason

/-- The module-linter half of the post-command check (addendum V2c.5): after
the root's last command, check that one of the root's top-level commands was
parsed as the gate command. Otherwise the command is missing, was parsed by
another parser, or is nested in another command, such as
`#guard_msgs (drop all) in`, which can discard its verdict. -/
private def checkRootCommands (commands : Array Syntax) : CommandElabM Unit := do
  let some rootFile ← rootFile? | return
  unless commands.any (·.getKind == gateKind) do
    runReplacedGate rootFile
      "no top-level command of the root was parsed as #whatwg_streams_axiom_gate"

initialize
  addLinter { name := `WhatwgTest.Audit.rootGateCommandCheck, run := checkRootGateCommand }
  addModuleLinter { name := `WhatwgTest.Audit.rootCommandsCheck, run := checkRootCommands }

end WhatwgTest.Audit
