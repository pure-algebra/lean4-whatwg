import WhatwgGates.Trust.Report

/-!
# Gates.Trust.ConfigShape

Rule 3 of addendum V2c of `test/contracts/trust-gate-hardening.contract.md`,
the configuration shape (V2c.4): wherever the token `(` is immediately followed
by the key `config` and then `:=`, the value must be a literal brace group
without `with`, closed by `)`.

The rule reads only the tags of one source's tokens of code, which the token
scan of `WhatwgGates/Trust/Tokens.lean` records, and returns the failing sites
as `TokenHit`s whose word is the reason; that module words the findings. It
imports nothing beyond `Init` and the report types.
-/

namespace Gates.Trust

open Lean (Syntax)

/-- One token of code as the configuration-shape rule reads it. -/
inductive ShapeTag where
  | openParen
  | configKey
  | assign
  | openBrace
  | closeBrace
  | closeParen
  | withKeyword
  | other
  deriving BEq, Inhabited

/-- The key `config` is an identifier whose `Name`, escapes removed, is `config`
(so `«config»` is one too), or an atom `config` should a grammar ever make it a
keyword. -/
def shapeTagOf : Syntax → ShapeTag
  | .atom _ "(" => .openParen
  | .atom _ ":=" => .assign
  | .atom _ "{" => .openBrace
  | .atom _ "}" => .closeBrace
  | .atom _ ")" => .closeParen
  | .atom _ "with" => .withKeyword
  | .atom _ "config" => .configKey
  | .ident _ _ name _ => if name == `config then .configKey else .other
  | _ => .other

/-- Rule 3 of addendum V2c over one source's tokens of code, given the tag of
every token and the sites, each the index of a `(` immediately followed by the
key `config` and then `:=`, with its position: the next token is `{`, the brace
group it opens contains no `with`, and the token after its matching `}` is `)`.
Every site is checked, a site inside another site's group included. Each failing
site is one finding, positioned at its `(`, whose word says which conditions
failed. -/
def configShapeFindings (tags : Array ShapeTag) (sites : Array (Nat × SourcePosition)) :
    Array TokenHit := Id.run do
  let tagAt (index : Nat) : ShapeTag := tags[index]?.getD .other
  let mut found : Array TokenHit := #[]
  for (index, position) in sites do
    if tagAt (index + 3) != .openBrace then
      found := found.push (position.hit "the value does not open with `{`")
      continue
    let mut depth := 0
    let mut sawWith := false
    let mut closing : Option Nat := none
    for cursor in [index + 3:tags.size] do
      match tagAt cursor with
      | .openBrace => depth := depth + 1
      | .closeBrace =>
          depth := depth - 1
          if depth == 0 then
            closing := some cursor
            break
      | .withKeyword => sawWith := true
      | _ => pure ()
    let mut reasons : Array String := #[]
    if sawWith then
      reasons := reasons.push "its brace group contains `with`"
    match closing with
    | none => reasons := reasons.push "its brace group is not closed, so `)` does not follow a closing `}`"
    | some cursor =>
        if tagAt (cursor + 1) != .closeParen then
          reasons := reasons.push "`)` does not follow the closing `}`"
    unless reasons.isEmpty do
      found := found.push (position.hit ("; ".intercalate reasons.toList))
  return found

end Gates.Trust
