import Lean
import Whatwg.Auto.RuleSets

/-!
# WhatwgTest.Audit.AutoCensus

`#whatwg_auto_census Some.Module using tac` takes every theorem that the named, imported
module declares, makes a goal of its statement, and runs `tac` on it under a heartbeat cap. It
reports the theorems that `tac` closes, each with the number of source lines its present
declaration takes and the axioms the found proof reaches, longest first; then the totals.

It is a measuring instrument (ruling R-S10 of `COORDINATION.md`), after
`src/Effect4/Laws/Auto/Census.lean` of lean4-effect4. It shows where `aesop` with the banks
registered so far already does the work of a long proof, and it checks a candidate bank
against a whole module at once. It changes nothing: every attempt is rolled back. It is never
a gate, and no module of the tree runs it: `workshop/AutoCensus.lean` holds an invocation.

    #whatwg_auto_census Whatwg.Svg.Data.Mask using aesop (rule_sets := [Whatwg.Mask])
    #whatwg_auto_census Whatwg.Html.Svg heartbeats 40000 using (intros; aesop)

A found proof counts only if the theorem could carry it in place: it uses neither the theorem
itself nor a declaration of the module that follows it.

What it does not report: a theorem that the tactic closes only after an `intro` or an
induction that the caller must name. The statement alone is the goal.
-/

open Lean Elab Meta Command Term

namespace WhatwgTest.Audit.AutoCensus

/-- The axioms a term reaches: those of every constant it mentions, by Lean's own collector.
This is a report and no verdict: the axiom gate judges a proof when it lands. -/
def axiomsOf (e : Expr) : CoreM (Array Name) := do
  let mut found : Array Name := #[]
  for c in e.getUsedConstants do
    for a in ← Lean.collectAxioms c do
      unless found.contains a do found := found.push a
  return found.qsort (·.toString < ·.toString)

/-- The source line a constant of the current module is declared at: its own, or that of the
declaration it was generated from (`foo.eq_1`, `foo.match_1` carry no range of their own). -/
def declaredAt : Name → CoreM (Option Nat)
  | name@(.str parent _) => do
    if let some r ← findDeclarationRanges? name then return some r.range.pos.line
    declaredAt parent
  | name => do
    if let some r ← findDeclarationRanges? name then return some r.range.pos.line
    return none

/-- Does `proof`, found for a theorem declared at line `startLine` of module `modIdx`, use that
theorem itself or anything of the module declared after it? In place, the proof would have
neither. -/
def usesWhatFollows (proof : Expr) (modIdx : ModuleIdx) (startLine : Nat) : CoreM Bool := do
  let env ← getEnv
  for c in proof.getUsedConstants do
    if env.getModuleIdxFor? c == some modIdx then
      if let some line ← declaredAt c then
        if line ≥ startLine then return true
  return false

/-- One attempt, rolled back: the axioms of the proof that `tac` finds for a goal of type
`type`, if it finds one that the theorem declared at `startLine` could carry in place. The
search is speculative, after `ProofGraph.search` of lean4-effect4: it runs without error
recovery and without asynchronous elaboration, and every declaration and metavariable it makes
is restored. The cap is in the units of the option `maxHeartbeats`; zero means no limit. -/
def attempt (type : Expr) (tac : Syntax) (cap : Nat) (modIdx : ModuleIdx) (startLine : Nat) :
    TermElabM (Option (Array Name)) :=
  withoutModifyingState do
    tryCatchRuntimeEx
      (withOptions (fun o => Elab.async.set (maxHeartbeats.set o cap) false) <|
        -- Lean caches this limit apart from the options; `withOptions` does not refresh it.
        withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := Core.getMaxHeartbeats ctx.options }) <|
        withCurrHeartbeats do
          let goal ← mkFreshExprMVar type
          let rest ← Tactic.run goal.mvarId! <| Tactic.withoutRecover (Tactic.evalTactic tac)
          unless rest.isEmpty do return none
          let proof ← instantiateMVars goal
          if proof.hasMVar || proof.hasFVar then return none
          if ← usesWhatFollows proof modIdx startLine then return none
          let mut axioms ← axiomsOf type
          for a in ← axiomsOf proof do
            unless axioms.contains a do axioms := axioms.push a
          -- a proof that rests on a placeholder is no proof
          if axioms.any (fun a => a.toString == "sorryAx") then return none
          return some (axioms.qsort (·.toString < ·.toString)))
      (fun _ => return none)
syntax (name := autoCensus)
  "#whatwg_auto_census " ident (" heartbeats " num)? " using " tacticSeq : command

@[command_elab autoCensus] def elabAutoCensus : CommandElab := fun stx => do
  let modName := stx[1].getId
  let cap := if stx[2].isNone then 20000 else stx[2][1].toNat
  let tac := stx[4]
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modName
    | throwError "#whatwg_auto_census: {modName} is not an imported module"
  let theorems := env.constants.map₁.fold (init := #[]) fun acc name info =>
    match info with
    | .thmInfo thm =>
      if env.getModuleIdxFor? name == some modIdx && !name.isInternalDetail then
        acc.push (name, thm.type)
      else acc
    | _ => acc
  -- only what a person wrote: a theorem with a source range of its own
  let mut written : Array (Nat × Nat × Name × Expr) := #[]
  for (name, type) in theorems do
    if let some r ← findDeclarationRanges? name then
      written := written.push (r.range.pos.line, r.range.endPos.line, name, type)
  let mut found : Array (Nat × Nat × Name × Array Name) := #[]
  for (first, last, name, type) in written do
    if let some axioms ← liftTermElabM (attempt type tac cap modIdx first) then
      found := found.push (first, last, name, axioms)
  let sorted := found.qsort fun a b => a.2.1 - a.1 > b.2.1 - b.1
  let mut report := m!"{modName}: {found.size} of {written.size} theorems closed from their \
    statements; {sorted.foldl (fun n r => n + (r.2.1 - r.1 + 1)) 0} source lines they now take"
  -- one row per theorem: lines, first-last line of the declaration, name, axioms of the found proof
  for (first, last, name, axioms) in sorted do
    report := report ++ m!"\n  {last - first + 1}\t{first}-{last}\t{name}\t{axioms}"
  logInfo report

end WhatwgTest.Audit.AutoCensus
