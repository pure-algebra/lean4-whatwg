import WhatwgGates.Common

/-!
# Gates.EmitLean

The spelling of generated Lean source that the schema emitters share: a constructor name for a
markup name, an enumeration, its census, a name table, a membership function and a character
pattern. `Gates.HtmlStandardEmit` and `Gates.SvgDefinitionsEmit` both write through these, so
the two generated schemas read alike. The definitions moved here from
`WhatwgGates/HtmlStandardEmit.lean` unchanged at slice S2 of `docs/SVG-PACKAGE-PLAN.md`: the
HTML drift gate checks that its outputs kept every byte.

Pure functions over strings. This module reads no file and writes none.
-/

namespace Gates.EmitLean

open Gates.Common

def leanKeywords : List String :=
  ["class", "section", "open", "for", "in", "at", "if", "then", "else", "do", "let", "fun",
   "match", "with", "end", "structure", "abbrev", "def", "theorem", "where", "namespace",
   "variable", "import", "instance", "example", "axiom", "by", "have", "show", "from", "mutual",
   "deriving", "private", "protected", "partial", "unsafe", "noncomputable", "inductive",
   "opaque", "macro", "syntax", "attribute", "local", "scoped", "universe", "calc", "suffices",
   "obtain", "exists", "forall", "hiding", "renaming", "using", "extends", "return", "break",
   "continue", "unless", "set_option", "omit", "include", "export", "nomatch", "nofun", "rec",
   "notation", "infix", "prefix", "postfix", "elab", "true", "false", "sorry", "admit", "try",
   "catch", "finally", "throw", "pure", "unfold", "generalizing", "type", "data", "this",
   "meta", "nonrec", "init", "run_cmd", "run_elab", "run_meta"]

/-- The Lean constructor name of a markup name: dashes to underscores,
guillemets when the result is a Lean keyword. -/
def ctorName (name : String) : String :=
  let base := name.replace "-" "_"
  if leanKeywords.contains base then "«" ++ base ++ "»" else base

/-- A set-membership function: constructor dispatch, eight members per line. -/
def emitBoolSet (fn : String) (doc : String) (domain : String) (members : List String) (domainCtors : List String) : String :=
  let members := domainCtors.filter members.contains
  if members.isEmpty then
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool := fun _ => false\n\n"
  else if members.length == domainCtors.length then
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool := fun _ => true\n\n"
  else
    let chunks := Id.run do
      let mut lines : List String := []
      let mut cur : List String := []
      for m in members do
        cur := cur ++ ["." ++ ctorName m]
        if cur.length == 8 then
          lines := lines ++ [String.intercalate " | " cur]
          cur := []
      if !cur.isEmpty then lines := lines ++ [String.intercalate " | " cur]
      lines
    let alts := String.intercalate "\n  | " chunks
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool\n  | {alts} => true\n  | _ => false\n\n"

/-- A name as a Lean `List Char` pattern: `['a', 'b']`. -/
def charsPattern (name : String) : String :=
  "[" ++ ", ".intercalate (name.toList.map fun c => "'" ++ (if c == '\'' then "\\'" else toString c) ++ "'") ++ "]"

def emitEnum (name : String) (doc : String) (ctors : List String) : String :=
  let lines := Id.run do
    let mut out : List String := []
    let mut cur : List String := []
    for c in ctors do
      cur := cur ++ [ctorName c]
      if cur.length == 8 then
        out := out ++ ["  | " ++ String.intercalate " | " cur]
        cur := []
    if !cur.isEmpty then out := out ++ ["  | " ++ String.intercalate " | " cur]
    out
  s!"/-- {doc} -/\ninductive {name} where\n{String.intercalate "\n" lines}\n  deriving DecidableEq, Repr, Inhabited, Hashable\n\n"

def emitStringFn (fn : String) (doc : String) (domain : String) (rows : List (String × String)) : String :=
  let alts := rows.map fun (c, s) => s!"  | .{ctorName c} => \"{s}\""
  s!"/-- {doc} -/\ndef {fn} : {domain} → String\n{String.intercalate "\n" alts}\n\n"

def emitAll (fn : String) (doc : String) (domain : String) (ctors : List String) : String :=
  let items := ctors.map fun c => "." ++ ctorName c
  let lines := Id.run do
    let mut out : List String := []
    let mut cur : List String := []
    for i in items do
      cur := cur ++ [i]
      if cur.length == 8 then
        out := out ++ ["   " ++ String.intercalate ", " cur ++ ","]
        cur := []
    if !cur.isEmpty then out := out ++ ["   " ++ String.intercalate ", " cur]
    out
  let body := String.intercalate "\n" lines
  let body := if body.endsWith "," then dropLastChars body 1 else body
  s!"/-- {doc} -/\ndef {fn} : List {domain} :=\n  [{dropChars body 3}]\n\n"

end Gates.EmitLean
