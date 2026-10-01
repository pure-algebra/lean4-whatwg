import WhatwgGates.Trust.Tokens

/-!
# Gates.Trust.Root

The root rule of the trust gate, rule 4 of addendum V2c of
`test/contracts/trust-gate-hardening.contract.md` (V2c.5), in its judging part:
the root `WhatwgTest.lean` holds only imports, comments, documentation and the
gate command `#whatwg_streams_axiom_gate` as its last command, and the root
module has declared no constant when the gate runs.

The lexical half reads the root's text, which the host hands in. The constants
the root module has declared are a read only a process that elaborates the root
can make, so the host hands them in too: the in-tree command reads them from its
environment, and an executable that never imports the root hands in none
(addendum V2e.5). The post-command check of V2c.5, which notices a replaced gate
command, is the in-tree command's own and is not here.
-/

namespace Gates.Trust

open Lean

/-- The one token of the gate command. -/
def gateCommandToken : String :=
  "#whatwg_streams_axiom_gate"

/-- One token of the root as the root pass reads it. -/
inductive RootTag where
  | importKeyword
  | identifier
  | gateCommand
  | other
  deriving BEq, Inhabited

/-- How a diagnostic shows one token: an atom's text, an identifier's spelling,
or the text of a literal. -/
def tokenText : Syntax → String
  | .atom _ text => text
  | .ident _ raw _ _ => raw.toString
  | .node _ kind arguments =>
      match (arguments[0]? : Option Syntax) with
      | some (Syntax.atom _ text) => text
      | _ => kind.toString
  | .missing => "<missing>"

def rootTagOf (token : Syntax) : RootTag :=
  if token.isToken "import" then .importKeyword
  else if token.isToken gateCommandToken then .gateCommand
  else if token.isIdent then .identifier
  else .other

/-- Pass 0 over the root's tokens of code (rule 4 of addendum V2c): `import` and
a module name, any number of times, then the gate command and nothing after it. -/
def rootShapeFindings (tokens : Array (RootTag × String × SourcePosition)) :
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
def rootFindings (environment : Environment) (tokenTable : Parser.TokenTable)
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

end Gates.Trust
