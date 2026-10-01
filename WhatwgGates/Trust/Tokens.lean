import WhatwgGates.Trust.Axioms
import WhatwgGates.Trust.ConfigShape
import WhatwgGates.Trust.Sources

/-!
# Gates.Trust.Tokens

The token passes of the trust gate over the audited sources (sections 4.2 and
4.3 of `test/contracts/trust-gate-hardening.contract.md`, addendum V2b.3, and
the token half of rule 1 of addendum V2c): the refused trust words, the
modifier keywords and the metaprogramming keywords; Lean's own tokenizer over
one source's text; the one scan that records, per source, every modifier,
refused token, metaprogramming keyword and configuration site of rule 3; and
the passes that word those records as findings, with the checks of the
source-token exemptions.

The scan reads a source's text and the token table the host hands in, and no
elaboration state: the in-tree command passes the final table of its loaded
environment, and an executable over built files passes the table it rebuilds
from their raw parser entries (addendum V2e.5, step 4).
-/

namespace Gates.Trust

open Lean

/-- A word the trust-token pass refuses (contract section 4.2). -/
structure RefusedWord where
  /-- The word as a diagnostic prints it. -/
  printed : String
  /-- The `Name` an identifier must equal, escapes removed, to carry the word. -/
  name : Name
  /-- For a forbidden axiom, the short name: an identifier whose last component
  it is carries the word as well. -/
  lastComponent? : Option String := none

def lastStringComponent? : Name → Option String
  | .str _ component => some component
  | _ => none

/-- A dotted spelling as a `Name`, one component per dot. -/
def dottedName (text : String) : Name :=
  (text.splitOn ".").foldl Name.mkStr Name.anonymous

def refusedWord (printed : String) : RefusedWord :=
  { printed, name := dottedName printed }

def refusedAxiomWord (axiomName : Name) : RefusedWord :=
  { printed := axiomName.toString, name := axiomName,
    lastComponent? := lastStringComponent? axiomName }

/-- The words that open a trust channel no constant records (ruling R-V2), each
refused as a keyword and as an identifier: compiler evaluation (`native_decide`,
`bv_decide`, `bv_decide?`, `bv_check`, and the `native` configuration flag in
every spelling), an admitted goal, an assumption, a replaced body, a
declaration the kernel never checks, and the forbidden axioms by name.

Addendum V2b (ruling R-V6) adds the spellings by which an `example` admits a
goal once a warning switch is thrown, and the switches themselves: the tactics
`admit`, `impossible`, `apply?`, `try?` and `grind?`; the options
`debug.byAsSorry`, `debug.terminalTacticsAsSorry`, `warn.sorry` and
`warningAsError`; `sorryAx` by name; and the compiler-evaluation functions
`Lean.reduceBool` and `Lean.reduceNat`, each by its last component as the
forbidden axioms are. `stop` is not refused: the tooling tree uses it as a
local name, and Lean's own warning stops it while `warningAsError` cannot be
switched off in code. -/
def refusedWords : List RefusedWord :=
  ["native_decide", "bv_decide", "bv_decide?", "bv_check", "native", "sorry", "axiom",
    "implemented_by", "extern", "debug.skipKernelTC", "admit", "impossible", "apply?", "try?",
    "grind?", "debug.byAsSorry", "debug.terminalTacticsAsSorry", "warn.sorry",
    "warningAsError"].map refusedWord ++
  (forbiddenAxioms ++ [``Lean.reduceBool, ``Lean.reduceNat]).map refusedAxiomWord

/-- Whether one token of code carries the word. -/
def RefusedWord.carriedBy (word : RefusedWord) : Syntax → Bool
  | .atom _ text => text == word.printed || word.lastComponent? == some text
  | .ident _ _ name _ =>
      name == word.name ||
        (word.lastComponent?.isSome && lastStringComponent? name == word.lastComponent?)
  | _ => false

/-- The atom texts that carry a refused word: every word as printed and every
short name of the last-component shape. -/
def refusedAtomTexts : Std.HashSet String :=
  refusedWords.foldl (init := {}) fun texts word =>
    match word.lastComponent? with
    | some component => (texts.insert word.printed).insert component
    | none => texts.insert word.printed

/-- The identifier names that carry a refused word as a whole name. -/
def refusedIdentifierNames : Std.HashSet Name :=
  refusedWords.foldl (init := {}) fun names word => names.insert word.name

/-- The last components that carry a refused word of the last-component shape. -/
def refusedLastComponents : Std.HashSet String :=
  refusedWords.foldl (init := {}) fun components word =>
    match word.lastComponent? with
    | some component => components.insert component
    | none => components

/-- Whether a token of code carries some refused word: exactly the disjunction of
`RefusedWord.carriedBy` over `refusedWords`, decided by set membership so that
the per-word test runs only on a token that carries one. -/
def carriesRefusedWord : Syntax → Bool
  | .atom _ text => refusedAtomTexts.contains text
  | .ident _ _ name _ =>
      refusedIdentifierNames.contains name ||
        match lastStringComponent? name with
        | some component => refusedLastComponents.contains component
        | none => false
  | _ => false

/-- The declaration modifiers the modifier pass refuses, as keywords only:
`«unsafe»` and `«partial»` stay names. -/
def modifierWords : List String :=
  ["unsafe", "partial"]

/-- The metaprogramming keywords of rule 1 (addendum V2c.2), refused in code
outside a listed module with the whole-name shape of section 4.2: an atom whose
text is the keyword, or an identifier whose `Name`, escapes removed, equals the
keyword's. The first group declares syntax, a macro, an elaborator or an
attribute; the second runs a metaprogram at elaboration. `local` and `scoped`
are separate atoms and stay admitted, so the prefixed forms are caught through
the keyword. Not refused: `meta`, `deriving`, `open`, `attribute`, `#guard`,
`#guard_msgs` and `#check_failure`, which the tree uses as ordinary code; and
the attribute and category names `command_elab`, `term_elab`, `tactic`, `init`,
`builtin_init` and `syntax_cat`, identifiers with ordinary uses whose
registrations the environment half refuses. -/
def metaprogrammingKeywords : List String :=
  ["syntax", "macro", "macro_rules", "elab", "elab_rules", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "declare_syntax_cat", "binder_predicate",
    "declare_simp_like_tactic", "simproc", "dsimproc", "simproc_decl", "dsimproc_decl",
    "builtin_simproc", "builtin_dsimproc", "builtin_simproc_decl", "builtin_dsimproc_decl",
    "register_simp_attr", "register_option", "register_builtin_option", "register_label_attr",
    "register_linter_set", "register_grind_attr", "register_sym_simp_attr",
    "register_parser_alias", "register_tactic_tag", "register_error_explanation",
    "declare_config_elab", "declare_command_config_elab",
    "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab", "#eval", "#eval!", "initialize",
    "builtin_initialize", "test_extern"]

/-- The metaprogramming keywords as atom texts. -/
def metaprogrammingKeywordTexts : Std.HashSet String :=
  metaprogrammingKeywords.foldl (init := {}) fun texts keyword => texts.insert keyword

/-- Each metaprogramming keyword by the `Name` an identifier must equal to carry it. -/
def metaprogrammingKeywordsByName : Std.HashMap Name String :=
  metaprogrammingKeywords.foldl (init := {}) fun byName keyword =>
    byName.insert (dottedName keyword) keyword

/-- The metaprogramming keyword one token of code carries, if any. -/
def metaprogrammingKeywordOf? : Syntax → Option String
  | .atom _ text => if metaprogrammingKeywordTexts.contains text then some text else none
  | .ident _ _ name _ => metaprogrammingKeywordsByName.get? name
  | _ => none

/-- Run Lean's own tokenizer over one source text and fold `step` over every
token of code. Documentation comments and module documentation are syntax nodes
rather than whitespace, so Lean's own parsers consume them and their prose never
becomes tokens. Each round consumes at least one byte or ends the scan, so the
byte count bounds the rounds; a round that consumes nothing, or a source that
outlasts its rounds, is a failure, never a silent end. Returns the folded state
and, when the tokenizer stopped before the end, the diagnostic that says where. -/
def foldCodeTokens {σ : Type} (environment : Environment) (tokenTable : Parser.TokenTable)
    (fileName input : String) (init : σ) (step : σ → Syntax → SourcePosition → σ) :
    σ × Option String := Id.run do
  let inputContext := Parser.mkInputContext input fileName
  let parserContext : Parser.ParserModuleContext :=
    { env := environment, options := {} }
  let fail (pos : String.Pos.Raw) (reason : String) : String :=
    let position := inputContext.fileMap.toPosition pos
    s!"Whatwg source trust gate: tokenization failed in {fileName}:{position.line}:{position.column + 1}: {reason}"
  let mut folded := init
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  let rounds := input.utf8ByteSize + 1
  for _ in [0:rounds] do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      return (folded, some (fail state.pos (toString error)))
    state := skipped
    if inputContext.atEnd state.pos then
      return (folded, none)
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
          return (folded, some (fail state.pos (toString error)))
        let token := next.stxStack.back
        let position := inputContext.fileMap.toPosition start
        folded := step folded token { line := position.line, column := position.column + 1 }
        projectionEnd :=
          if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
        state := next.popSyntax
    unless start.byteIdx < state.pos.byteIdx do
      return (folded, some (fail start "the tokenizer consumed nothing"))
  return (folded, some (fail state.pos s!"the scan did not end within {rounds} rounds"))

/-- What the tokenizer found in one audited source. -/
structure SourceScan where
  source : System.FilePath
  modifiers : Array TokenHit := #[]
  trustTokens : Array TokenHit := #[]
  /-- Metaprogramming keywords of rule 1 in code. -/
  metaprogrammingKeywords : Array TokenHit := #[]
  /-- Configuration sites of rule 3 that fail the shape; the word is the reason. -/
  configShapes : Array TokenHit := #[]
  /-- Why the tokenizer stopped before the end of the source, if it did. -/
  failure? : Option String := none

/-- The state `scanSource` folds over one source's tokens of code. -/
structure ScanState where
  modifiers : Array TokenHit := #[]
  trustTokens : Array TokenHit := #[]
  metaprogrammingKeywords : Array TokenHit := #[]
  /-- The configuration-shape tag of every token so far. -/
  shapeTags : Array ShapeTag := #[]
  /-- The position of the latest `(`. -/
  latestParen : SourcePosition := { line := 0, column := 0 }
  /-- Every `(` `config` `:=` site so far: the index of its `(`, and where it is. -/
  configSites : Array (Nat × SourcePosition) := #[]

/-- Record every modifier keyword, refused trust token and metaprogramming
keyword of one token of code, and its tag for the configuration-shape rule. -/
def scanStep (state : ScanState) (token : Syntax) (position : SourcePosition) : ScanState :=
  let state := match modifierWords.find? (token.isToken ·) with
    | some modifier => { state with modifiers := state.modifiers.push (position.hit modifier) }
    | none => state
  let state :=
    if carriesRefusedWord token then
      refusedWords.foldl (init := state) fun state word =>
        if word.carriedBy token then
          { state with trustTokens := state.trustTokens.push (position.hit word.printed) }
        else state
    else state
  let state := match metaprogrammingKeywordOf? token with
    | some keyword =>
        { state with
          metaprogrammingKeywords := state.metaprogrammingKeywords.push (position.hit keyword) }
    | none => state
  let tag := shapeTagOf token
  let index := state.shapeTags.size
  let state :=
    if tag == .assign && index ≥ 2 && state.shapeTags[index - 1]? == some .configKey &&
        state.shapeTags[index - 2]? == some .openParen then
      { state with configSites := state.configSites.push (index - 2, state.latestParen) }
    else state
  let state := if tag == .openParen then { state with latestParen := position } else state
  { state with shapeTags := state.shapeTags.push tag }

/-- Tokenize one source's text `input` with Lean's own tokenizer and record every
modifier keyword, every refused trust token, every metaprogramming keyword and
every configuration site that fails the shape, in code. -/
def scanSourceText (environment : Environment) (tokenTable : Parser.TokenTable)
    (source : System.FilePath) (input : String) : SourceScan :=
  let (state, failure?) :=
    foldCodeTokens environment tokenTable source.toString input {} scanStep
  { source, modifiers := state.modifiers, trustTokens := state.trustTokens,
    metaprogrammingKeywords := state.metaprogrammingKeywords,
    configShapes := configShapeFindings state.shapeTags state.configSites, failure? }

/-- Read one source and scan it with `scanSourceText`. -/
def scanSource (environment : Environment) (tokenTable : Parser.TokenTable)
    (source : System.FilePath) : IO SourceScan := do
  let input ← IO.FS.readFile source
  return scanSourceText environment tokenTable source input

/-- Pass 2: tokenization failures and the `unsafe` and `partial` keywords. -/
def modifierFindings (scans : Array SourceScan) : Array String :=
  scans.flatMap fun scan =>
    let failures := match scan.failure? with
      | some failure => #[failure]
      | none => #[]
    failures ++ scan.modifiers.map fun hit =>
      s!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` declaration modifier at line {hit.line}, column {hit.column}"

/-- Pass 5: validate the exemption list, then refuse every refused token outside
an exempted source and every exemption whose source needs none (contract
sections 4.2 and 4.3). -/
def trustTokenFindings (config : Config) (projectRoot : System.FilePath)
    (sources : AuditedSources) (scans : Array SourceScan) : Array String := Id.run do
  let mut findings : Array String := #[]
  let modulePaths := sources.modules.map (·.normalize)
  let entryPaths := sources.entryPoints.map (·.normalize)
  let mut exempted : Array (System.FilePath × Name) := #[]
  let mut listed : Array Name := #[]
  for exemption in config.sourceTokenExemptions do
    let moduleName := exemption.moduleName
    if isBlank exemption.reason then
      findings := findings.push
        s!"Whatwg source trust gate: source-token exemption for {moduleName} carries no reason"
    if listed.contains moduleName then
      findings := findings.push
        s!"Whatwg source trust gate: source-token exemption for {moduleName} is listed more than once"
      continue
    listed := listed.push moduleName
    let path := (Lean.modToFilePath projectRoot moduleName "lean").normalize
    let entryPath := (Lean.modToFilePath (projectRoot / "whatwgbin") moduleName "lean").normalize -- R-V3(c), 2026-10-01
    if entryPaths.contains path || entryPaths.contains entryPath then
      findings := findings.push
        s!"Whatwg source trust gate: source-token exemption for {moduleName} names an entry point under whatwgbin/, and no file under whatwgbin/ can be exempted" -- R-V3(c), 2026-10-01
    else if modulePaths.contains path then
      exempted := exempted.push (path, moduleName)
    else
      findings := findings.push
        s!"Whatwg source trust gate: source-token exemption names missing module {moduleName}"
  for scan in scans do
    match exempted.find? (·.1 == scan.source.normalize) with
    | some (_, moduleName) =>
        if scan.trustTokens.isEmpty then
          findings := findings.push
            s!"Whatwg source trust gate: stale source-token exemption for {moduleName}; its source contains no refused token"
    | none =>
        for hit in scan.trustTokens do
          findings := findings.push
            s!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` trust token at line {hit.line}, column {hit.column}"
  return findings

/-- Pass 5, the token half of rule 1 and rule 3 (addendum V2c.2 and V2c.4): a
metaprogramming keyword in code outside a listed module's source, and every
configuration site that fails the shape, in every audited source. -/
def keywordAndShapeFindings (config : Config) (projectRoot : System.FilePath)
    (sources : AuditedSources) (scans : Array SourceScan) : Array String := Id.run do
  let modulePaths := sources.modules.map pathKey
  let listedPaths := (config.metaprogrammingModules.map fun entry =>
    pathKey (Lean.modToFilePath projectRoot entry.moduleName "lean")).filter modulePaths.contains
  let mut findings : Array String := #[]
  for scan in scans do
    unless listedPaths.contains (pathKey scan.source) do
      for hit in scan.metaprogrammingKeywords do
        findings := findings.push
          s!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` metaprogramming keyword at line {hit.line}, column {hit.column}"
  for scan in scans do
    for hit in scan.configShapes do
      findings := findings.push
        s!"Whatwg source trust gate: {scan.source.toString} contains a non-literal `config` option at line {hit.line}, column {hit.column}: {hit.word}"
  return findings

end Gates.Trust
