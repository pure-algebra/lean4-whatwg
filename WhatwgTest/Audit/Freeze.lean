import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Meta.Match.MatcherInfo

/-!
# The freeze registry command

`#whatwg_freeze (@n : T)` freezes the declaration `n`. Its behaviour is frozen by
`test/contracts/freeze-registry.contract.md` (ruling R-W5, with R-W12) and
falsified by `WhatwgTest/Audit/FreezeContract.lean`; the design record is
`docs/research/2026-10-01-w6-freeze-registry-design.md`. The full form, every
clause optional, at most once, and in this order:

```text
#whatwg_freeze (@n : T)
  [axioms [a, …]]
  [mask M1 | mask M2 | mask none "reason"]
  [anchor "row-id"]
  [graph "edge"]
  [counterexamples ["id", …]]
```

## What a freeze pins

1. *The statement.* `T` is elaborated alone, as a type with no expected type,
   with every synthetic metavariable synthesised and no error turned into
   `sorry`. A leftover metavariable is refused, an expression hole and a
   universe hole each with its own diagnostic: a hole is filled by nothing, so
   it pins nothing. The result must be the declared type of `n` under
   `sameStatement`.
2. *The axiom set*, when the `axioms` clause is written: the listed names, each
   resolved as a global constant, must be exactly `Lean.collectAxioms n` as a
   set. The clause is required when `n` is a theorem and optional otherwise.
3. *The record.* On success the command prints nothing and adds one
   kernel-checked definition `<recording module>.frozen.<n> : Entry` (see
   `entryName`) that holds the resolved name, the actual axiom set when the
   clause was written (sorted by `Lean.Name.lt`), and the mask, anchor, graph
   and counterexample clauses as written. The registry is the set of these
   declarations; a declaration is frozen at most once per module.

## What a freeze does not pin

A definition's body (beyond its axiom set when the clause is written); a
theorem's proof beyond its axiom set; the binder names and binder annotations
of the declared type; the `let`/`have` flag; the identity of auxiliary
constants whose types and values agree; docstrings, attributes, declaration
ranges and the declaring module. It records the `anchor`, `graph` and
`counterexamples` clauses as written and checks none of them. Section 13 of the
contract is the full list.

## `sameStatement` and its two allowances

`sameStatement` is `Lean.Expr.eqv` (binder names and binder annotations
ignored, metadata compared) taken apart node by node so that two allowances can
apply below the root, and nothing else is unfolded: no constant other than an
auxiliary one is replaced by its value, and no beta, eta, zeta, iota,
projection or instance reduction is performed. Universe levels compare
structurally, so an ascription names the declaration's own universe
parameters.

1. *The `let`/`have` flag.* Two `let` nodes agree when their types, values and
   bodies do, whatever their non-dependency flags. The declaration elaborator
   records a statement's non-dependent `let` as a `have`; a standalone
   elaboration of the same text does not.
2. *Auxiliary constants.* Two auxiliary constants (a matcher, or a constant
   with an internal name such as `_sparseCasesOn_1` or `_private`) at equal
   universe level lists agree when their declared types and their values agree
   under this relation. A `match` in a battery is elaborated into a matcher of
   the battery's own, built on its own `_sparseCasesOn_N`, where the
   declaration has `<declaration>.match_N`; no text a battery can write names
   the declaration's matcher, so without this allowance a statement with a
   `match` could not be frozen at all.

Metadata is never dropped (R-W12): two metadata nodes agree only with the same
entries in the same order, and metadata on one side only is a refusal, exactly
as `Expr.eqv` treats it. The comparison recurses on a fuel argument and refuses
when the fuel runs out.

## Trust

This module is on the gate's `metaprogrammingModules` list because it declares
the command's syntax and its `command_elab` elaborator; it is bound by every
other trust rule. The only token it adds to the table is `#whatwg_freeze`; the
clause words are non-reserved, so no identifier anywhere becomes a keyword. It
declares no persistent environment extension: `initialize` declares an `opaque`
whose value Lean synthesises, which the gate refuses, so the registry lives in
ordinary declarations, added by `Lean.addDecl` with the kernel check on. The
command does not compile an entry; a battery reads one back by `rfl`. A battery
that only uses the command registers nothing and needs no list entry.
-/

open Lean Elab Command

namespace WhatwgTest.Audit.Freeze

/-- The observation mask a frozen declaration claims (design basis DB-04 and
the root router's representation rules). Not `Effects.Trace.Mask`, a filter of
trace events, nor a projection of `Whatwg.Streams.Semantics.Mask`. The clause
spells the first two `mask M1` and `mask M2`. -/
inductive ObservationMask where
  /-- M1: the chunk sequence plus the terminal outcome. -/
  | chunksAndOutcome
  /-- M2: the full settlement order. -/
  | settlementOrder
  /-- The declaration states no observation; the reason says why. -/
  | notApplicable (reason : String)
  deriving Inhabited, BEq, Repr

/-- One registry record. The statement is not stored: the battery text is the
authored copy, and the environment holds the declared type. -/
structure Entry where
  /-- The frozen declaration's resolved full name. -/
  declaration : Name
  /-- The exact axiom set, sorted by `Lean.Name.lt`, when the `axioms` clause
  was written; `none` when it was not. -/
  axioms : Option (List Name)
  /-- The `mask` clause. -/
  mask : Option ObservationMask := none
  /-- The `anchor` clause, as written. -/
  anchor : Option String := none
  /-- The `graph` clause, as written. -/
  graph : Option String := none
  /-- The `counterexamples` clause, in the order written; `[]` when absent. -/
  counterexamples : List String := []
  deriving Inhabited, BEq, Repr

instance : ToExpr ObservationMask where
  toExpr
    | .chunksAndOutcome => mkConst ``ObservationMask.chunksAndOutcome
    | .settlementOrder => mkConst ``ObservationMask.settlementOrder
    | .notApplicable reason => mkApp (mkConst ``ObservationMask.notApplicable) (toExpr reason)
  toTypeExpr := mkConst ``ObservationMask

/-- The entry as the closed term `Entry.mk d a m an g ce`, each argument the
`Lean.toExpr` form of its field. -/
private def entryExpr (entry : Entry) : Expr :=
  mkAppN (mkConst ``Entry.mk)
    #[toExpr entry.declaration, toExpr entry.axioms, toExpr entry.mask, toExpr entry.anchor,
      toExpr entry.graph, toExpr entry.counterexamples]

/-- The name of the entry that module `recording` holds for `declaration`:
`<recording>.frozen.<declaration>`. -/
def entryName (recording declaration : Name) : Name :=
  (recording ++ `frozen) ++ declaration

/-- Whether a constant is auxiliary for the second allowance of
`sameStatement`: a matcher, or a constant with an internal name. -/
private def isAuxiliary (constant : Name) : MetaM Bool :=
  return (← Meta.isMatcher constant) || constant.isInternal

/-- Statement identity: `Lean.Expr.eqv`, with the `let`/`have` flag ignored and
auxiliary constants compared by their types and values; nothing else is
unfolded (module documentation). The first argument is the fuel: each step
down the two terms costs one, and a comparison that runs out refuses. -/
def sameStatement : Nat → Expr → Expr → MetaM Bool
  | 0, _, _ => return false
  | fuel + 1, left, right => do
    if left == right then return true
    match left, right with
    | .app f x, .app g y =>
        if !(← sameStatement fuel f g) then return false
        sameStatement fuel x y
    | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ =>
        if !(← sameStatement fuel t₁ t₂) then return false
        sameStatement fuel b₁ b₂
    | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ =>
        if !(← sameStatement fuel t₁ t₂) then return false
        sameStatement fuel b₁ b₂
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ =>
        -- Allowance 1: the non-dependency flags are not compared.
        if !(← sameStatement fuel t₁ t₂) then return false
        if !(← sameStatement fuel v₁ v₂) then return false
        sameStatement fuel b₁ b₂
    | .proj s₁ i₁ x, .proj s₂ i₂ y =>
        if s₁ != s₂ || i₁ != i₂ then return false
        sameStatement fuel x y
    | .mdata d₁ x, .mdata d₂ y =>
        -- Metadata is compared, never dropped: the same entries in the same order.
        if d₁.entries != d₂.entries then return false
        sameStatement fuel x y
    | .const n₁ ls₁, .const n₂ ls₂ =>
        -- Allowance 2: two auxiliary constants agree by their types and values.
        if ls₁ != ls₂ then return false
        if !(← isAuxiliary n₁) || !(← isAuxiliary n₂) then return false
        let some c₁ := (← getEnv).find? n₁ | return false
        let some c₂ := (← getEnv).find? n₂ | return false
        let some v₁ := c₁.value? | return false
        let some v₂ := c₂.value? | return false
        if !(← sameStatement fuel (c₁.instantiateTypeLevelParams ls₁)
            (c₂.instantiateTypeLevelParams ls₂)) then
          return false
        sameStatement fuel (v₁.instantiateLevelParams c₁.levelParams ls₁)
          (v₂.instantiateLevelParams c₂.levelParams ls₂)
    | _, _ => return false

/-- The fuel the command passes to `sameStatement`: far above the depth of any
statement in the tree. -/
def statementFuel : Nat := 100000

/-- Names sorted by `Lean.Name.lt`, without duplicates. -/
private def sortedNames (names : Array Name) : List Name :=
  (names.qsort Name.lt).toList.foldr (init := []) fun name kept =>
    match kept with
    | next :: _ => if name == next then kept else name :: kept
    | [] => [name]

/-- A name list as plain text: `[`, the names joined by `, `, then `]`. -/
private def nameListText (names : List Name) : String :=
  "[" ++ ", ".intercalate (names.map toString) ++ "]"

/-- Whether a string is empty after trimming ASCII whitespace. -/
private def isBlank (text : String) : Bool :=
  text.toList.all Char.isWhitespace

/-- The command. The clause words are non-reserved symbols, so the only token
this syntax adds to the table is `#whatwg_freeze`; the `mask` clause reads an
identifier and an optional string, and the elaborator decides. -/
syntax (name := freezeCommand) "#whatwg_freeze " "(" "@" ident " : " term ")"
  (&"axioms" "[" ident,* "]")?
  (&"mask" ident (str)?)?
  (&"anchor" str)?
  (&"graph" str)?
  (&"counterexamples" "[" str,* "]")? : command

/-- The elaborator of `#whatwg_freeze`. It runs the checks of the contract's
section 7 in order and stops at the first refusal: resolve `n`; F1, an entry
for `n` exists in this module; elaborate `T` alone; F2 and F3, a hole; F4, not
the declared statement; F5 and F6, the axiom clause; F7 and F8, the mask
clause; then add the entry. -/
@[command_elab freezeCommand]
def elabFreeze : CommandElab := fun stx => do
  let nameStx := stx[3]
  let typeStx := stx[5]
  let axiomsStx := stx[7]
  let maskStx := stx[8]
  let anchorStx := stx[9]
  let graphStx := stx[10]
  let counterexamplesStx := stx[11]
  let declaration ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo nameStx
  let name := entryName (← getMainModule) declaration
  if (← getEnv).contains name then
    throwErrorAt nameStx m!"freeze: {declaration} is already frozen in this module"
  let info ← getConstInfo declaration
  -- The statement, elaborated alone. Auxiliary declarations it creates (a
  -- battery `match`'s matcher) are discarded with the environment.
  withoutModifyingEnv <| liftTermElabM <| Term.withoutErrToSorry do
    let type ← Term.elabType typeStx
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    if type.hasExprMVar then
      throwErrorAt typeStx
        m!"freeze: the statement of {declaration} has an expression hole; write every argument"
    if type.hasLevelMVar then
      throwErrorAt typeStx
        m!"freeze: the statement of {declaration} has a universe hole; write every universe level"
    unless ← sameStatement statementFuel type info.type do
      throwErrorAt typeStx
        m!"freeze: the statement of {declaration} is not the declared one{indentExpr info.type}"
  -- The axiom set: required for a theorem, optional otherwise.
  let axioms ← if axiomsStx.isNone then
      if info matches .thmInfo _ then
        throwErrorAt nameStx m!"freeze: {declaration} is a theorem; its axioms clause is required"
      pure none
    else
      let listed ← axiomsStx[2].getSepArgs.mapM fun axiomStx =>
        liftCoreM <| realizeGlobalConstNoOverloadWithInfo axiomStx
      let listed := sortedNames listed
      let actual := sortedNames (← collectAxioms declaration)
      if actual != listed then
        let extra := actual.filter (!listed.contains ·)
        let stale := listed.filter (!actual.contains ·)
        throwErrorAt axiomsStx
          m!"freeze: the axioms of {declaration} are {nameListText actual}; not listed {nameListText extra}, listed but not reached {nameListText stale}"
      pure (some actual)
  -- The mask clause: `M1`, `M2`, or `none` with a reason that is not blank.
  let mask ← if maskStx.isNone then pure none else do
    let word := maskStx[1].getId
    let reason? := if maskStx[2].isNone then none else maskStx[2][0].isStrLit?
    let malformed :=
      m!"freeze: the mask clause of {declaration} is not mask M1, mask M2 or mask none \"reason\""
    match reason? with
    | none =>
        if word == `M1 then pure (some ObservationMask.chunksAndOutcome)
        else if word == `M2 then pure (some ObservationMask.settlementOrder)
        else throwErrorAt maskStx malformed
    | some reason =>
        unless word == `none do throwErrorAt maskStx malformed
        if isBlank reason then
          throwErrorAt maskStx m!"freeze: the mask clause of {declaration} gives an empty reason"
        pure (some (ObservationMask.notApplicable reason))
  let anchor := if anchorStx.isNone then none else anchorStx[1].isStrLit?
  let graph := if graphStx.isNone then none else graphStx[1].isStrLit?
  let counterexamples : List String :=
    if counterexamplesStx.isNone then []
    else (counterexamplesStx[2].getSepArgs.filterMap (·.isStrLit?)).toList
  let entry : Entry := { declaration, axioms, mask, anchor, graph, counterexamples }
  let value := entryExpr entry
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl <| .defnDecl
    { name, levelParams := [], type := mkConst ``Entry, value,
      hints := .regular height, safety := .safe }

end WhatwgTest.Audit.Freeze
