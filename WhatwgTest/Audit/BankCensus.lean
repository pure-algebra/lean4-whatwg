import Aesop
import Whatwg.Auto.RuleSets

/-!
# WhatwgTest.Audit.BankCensus

`#whatwg_bank_census "Whatwg" "WhatwgTest"` reports, for every declared `Whatwg.*` Aesop rule
bank: its rules, its simp lemmas, and how many `rule_sets := [...]` clauses under each
directory name it. A bank with no rule is empty. A bank that no clause of the first directory
names is unused by the library. The second count shows whether its control exists
(`WhatwgTest/Auto/Banks.lean`).

It is a measuring instrument (ruling R-S10 of `COORDINATION.md`), after
`src/Effect4/Laws/Auto/BankCensus.lean` of lean4-effect4. It changes nothing and fails on
nothing, and no module of the tree runs it: `workshop/BankCensus.lean` holds an invocation.
Clauses are read from the source text, so a clause inside a comment is counted too.
-/

open Lean Elab Command

namespace WhatwgTest.Audit.BankCensus

/-- The bank names that a `rule_sets := [A, B]` clause lists, read from source text. -/
def ruleSetClauses (text : String) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for part in (text.splitOn "rule_sets := [").drop 1 do
    let inside := (part.splitOn "]").headD ""
    for item in inside.splitOn "," do
      let n := item.trimAscii.toString
      unless n.isEmpty do out := out.push n.toName
  return out

/-- Every bank name that the `.lean` files under `dir` name in a clause, with multiplicity. -/
def clausesUnder (dir : System.FilePath) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for f in ← dir.walkDir do
    if f.extension == some "lean" then
      out := out ++ ruleSetClauses (← IO.FS.readFile f)
  return out

syntax (name := bankCensus) "#whatwg_bank_census " str str : command

@[command_elab bankCensus] def elabBankCensus : CommandElab := fun stx => do
  let some library := stx[1].isStrLit? | throwError "bank census: expected a directory"
  let some tests := stx[2].isStrLit? | throwError "bank census: expected a directory"
  let inLibrary ← clausesUnder library
  let inTests ← clausesUnder tests
  let banks ← liftCoreM Aesop.Frontend.getDeclaredGlobalRuleSets
  let mut rows : Array String := #[]
  for (name, rs, _, _) in banks.qsort (fun a b => a.1.toString < b.1.toString) do
    unless (`Whatwg).isPrefixOf name do continue
    let rules := rs.ruleNames.foldl (fun n _ v => n + v.size) 0
    let simps := rs.simpTheorems.lemmaNames.fold (fun n _ => n + 1) 0
    let named := (inLibrary.filter (· == name)).size
    let controls := (inTests.filter (· == name)).size
    let flag := if rules + simps == 0 then "  (empty)"
      else if named == 0 then "  (unused by the library)" else ""
    rows := rows.push s!"{name}\t{rules} rules\t{simps} simp lemmas\t{named} library clauses\t{controls} test clauses{flag}"
  logInfo m!"bank census\n{"\n".intercalate rows.toList}"

end WhatwgTest.Audit.BankCensus
