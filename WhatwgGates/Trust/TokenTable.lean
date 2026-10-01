import WhatwgGates.Trust.Tokens

/-!
# Gates.Trust.TokenTable

Token-table hygiene, rule 2 of addendum V2c of
`test/contracts/trust-gate-hardening.contract.md` (V2c.3): every token of the
final token table, scoped entries included, that neither the `lean` binary nor
an `Init` module declares must be inert, so that no token hides a refused word
from the source passes, whoever declared it.

The host hands in the final table and the scoped tokens. The in-tree command
reads both from the parser extension's loaded state; an executable over built
files rebuilds the table from `Lean.Parser.builtinTokenTable` and the raw global
`.token` entries and takes the scoped tokens from the raw scoped entries
(addendum V2e.5, step 4). Which module declared a token is read here, through
`getModuleEntries` of the parser extension, which an import fills in whether or
not it loads the extensions.
-/

namespace Gates.Trust

open Lean

/-- The whole-name words of the inert test T3: every refused word as printed and
the two modifier keywords. -/
def inertWholeWords : List String :=
  refusedWords.map (·.printed) ++ modifierWords

/-- The last-component words of the inert test T3: the short names of the
forbidden axioms, of `sorryAx` and of the two kernel-evaluation hooks. -/
def inertLastComponents : List String :=
  refusedWords.filterMap (·.lastComponent?)

/-- The identifier read from index `start`, as the inert test T3 reads it:
components joined by `.` when the character after the dot may begin one, up to
a character that may not continue it or the end. Returns the spelling, the index
after it, and whether exactly one `.` follows it at the very end. -/
def readIdentifier (characters : Array Char) (start : Nat) : String × Nat × Bool :=
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
def inertForbiddenFragments : List (String × String) :=
  [(" ", "a space"), ("\t", "a tab"), ("\r", "a carriage return"), ("\n", "a line feed"),
    ("\"", "`\"`"), ("«", "`«`"), ("»", "`»`"), ("--", "`--`"), ("/-", "`/-`"), ("-/", "`-/`")]

/-- Why a token fails the inert test of addendum V2c.3, empty when it is inert.
`splitters` are the tokens of the table that contain a character that cannot
continue an identifier: an identifier may start right after one of them. -/
def inertFailures (splitters : Array String) (token : String) : Array String := Id.run do
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
def nonBaseTokens (environment : Environment) (finalTable : Parser.TokenTable)
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

/-- The pass after pass 2, token-table hygiene (rule 2 of addendum V2c): every
non-base token of the final table is inert. -/
def tokenTableFindings (tokens : Array String) (nonBase : Array (String × Array Name)) :
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

end Gates.Trust
