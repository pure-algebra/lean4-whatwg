import WhatwgTest.Audit.Freeze

/-!
# Freeze registry contract battery

Breaker-owned and frozen before implementation. Packet:
`test/contracts/freeze-registry.contract.md`, which is the authority on every
diagnostic below and on the meaning of every name this file ascribes. Ruling
R-W5 of `COORDINATION.md` adopts the command; design record
`docs/research/2026-10-01-w6-freeze-registry-design.md`.

This battery is a tooling contract. It asserts no WHATWG semantics and grants
no coverage state. Every control freezes a small declaration this file
declares itself, so nothing here depends on a production name.

It is red for one reason only: the module `WhatwgTest.Audit.Freeze`, which
declares the command `#whatwg_freeze` and every name ascribed in section 1,
does not exist yet. The builder creates that module; the builder does not edit
this file.

Sections:

1. the public declarations of `WhatwgTest.Audit.Freeze`, by exact ascription;
2. the fixtures, small declarations the controls freeze;
3. acceptance controls: each command prints nothing, and its entry reads back
   exactly what its clauses wrote;
4. refusal controls: each command is refused with its frozen diagnostic;
5. the counterexample witnesses `FREEZE-CE-001` to `FREEZE-CE-003`: today's
   `#check` accepts what the command refuses.

Every control was run against the design's prototype command (appendix A of
the design record, adapted to R-W5) before this file was committed.
-/

set_option autoImplicit false

universe u v

/-! ## 1. Public declarations

The record of section 4 of the packet. `WhatwgTest.Audit.Freeze` declares no
other public name except instances and what Lean generates for these. -/

#check (@WhatwgTest.Audit.Freeze.ObservationMask : Type)
#check (@WhatwgTest.Audit.Freeze.ObservationMask.chunksAndOutcome :
  WhatwgTest.Audit.Freeze.ObservationMask)
#check (@WhatwgTest.Audit.Freeze.ObservationMask.settlementOrder :
  WhatwgTest.Audit.Freeze.ObservationMask)
#check (@WhatwgTest.Audit.Freeze.ObservationMask.notApplicable :
  String → WhatwgTest.Audit.Freeze.ObservationMask)

#check (@WhatwgTest.Audit.Freeze.Entry : Type)
#check (@WhatwgTest.Audit.Freeze.Entry.mk :
  Lean.Name → Option (List Lean.Name) → Option WhatwgTest.Audit.Freeze.ObservationMask →
    Option String → Option String → List String → WhatwgTest.Audit.Freeze.Entry)
#check (@WhatwgTest.Audit.Freeze.Entry.declaration :
  WhatwgTest.Audit.Freeze.Entry → Lean.Name)
#check (@WhatwgTest.Audit.Freeze.Entry.axioms :
  WhatwgTest.Audit.Freeze.Entry → Option (List Lean.Name))
#check (@WhatwgTest.Audit.Freeze.Entry.mask :
  WhatwgTest.Audit.Freeze.Entry → Option WhatwgTest.Audit.Freeze.ObservationMask)
#check (@WhatwgTest.Audit.Freeze.Entry.anchor :
  WhatwgTest.Audit.Freeze.Entry → Option String)
#check (@WhatwgTest.Audit.Freeze.Entry.graph :
  WhatwgTest.Audit.Freeze.Entry → Option String)
#check (@WhatwgTest.Audit.Freeze.Entry.counterexamples :
  WhatwgTest.Audit.Freeze.Entry → List String)

#check (@WhatwgTest.Audit.Freeze.entryName : Lean.Name → Lean.Name → Lean.Name)
#check (@WhatwgTest.Audit.Freeze.sameStatement :
  Nat → Lean.Expr → Lean.Expr → Lean.MetaM Bool)
#check (@WhatwgTest.Audit.Freeze.statementFuel : Nat)
#check (@WhatwgTest.Audit.Freeze.elabFreeze : Lean.Elab.Command.CommandElab)
#check (@WhatwgTest.Audit.Freeze.freezeCommand : Lean.ParserDescr)

-- The naming rule, as data: `<recording module>.frozen.<declaration>`.
#guard WhatwgTest.Audit.Freeze.entryName `A.B `c.d == `A.B.frozen.c.d
#guard WhatwgTest.Audit.Freeze.entryName `WhatwgTest.Audit.FreezeContract
    `Whatwg.Streams.Data.Queue.empty_entries ==
  `WhatwgTest.Audit.FreezeContract.frozen.Whatwg.Streams.Data.Queue.empty_entries

-- The comparison depth of the judgment.
#guard WhatwgTest.Audit.Freeze.statementFuel == 100000

-- Ruling R-W5: no Lean declaration is named `m1` or `m2`; the masks are named
-- by meaning.
/--
error: Unknown constant `WhatwgTest.Audit.Freeze.ObservationMask.m1`
-/
#guard_msgs in
#check (@WhatwgTest.Audit.Freeze.ObservationMask.m1 : WhatwgTest.Audit.Freeze.ObservationMask)

/--
error: Unknown constant `WhatwgTest.Audit.Freeze.ObservationMask.m2`
-/
#guard_msgs in
#check (@WhatwgTest.Audit.Freeze.ObservationMask.m2 : WhatwgTest.Audit.Freeze.ObservationMask)

namespace WhatwgTest.Audit.FreezeContract

open WhatwgTest.Audit.Freeze

/-! ## 2. Fixtures

Each control below freezes one of these. A refused command adds nothing, so a
fixture that is refused several times stays unfrozen. -/

namespace Fixture

/-- Acceptance A1: the ascription is the declared type, binder names included
(`Expr.equal`). -/
theorem exact (n : Nat) : n + 0 = n := rfl

/-- Acceptance A2: the ascription renames the binder (`Expr.eqv`). -/
theorem renamed (m : Nat) : m + 0 = m := rfl

/-- Acceptance A3: the ascription makes the implicit argument explicit
(`Expr.eqv` ignores binder annotations). -/
theorem implicitMadeExplicit {α : Type} (xs : List α) : [] ++ xs = xs := rfl

/-- Acceptance A4: a statement with a `let`, which the declaration elaborator
records as a non-dependent `let` and a standalone elaboration does not. -/
theorem withLet : (let x := 2; x + x) = 4 := rfl

/- Lean reuses an identical matcher within one module (its matcher cache is
module-local and keyed on the matcher's value and on
`bootstrap.genMatcherCode`), so a battery that imports a declaration always
elaborates its own matcher, and a battery that declares the statement itself
would silently reuse the declaration's. Declaring this fixture with matcher
code generation off gives its matcher another cache key, so the command's
standalone elaboration builds a second matcher with an equal body, as it does
for every imported declaration. -/
set_option bootstrap.genMatcherCode false in
/-- Acceptance A5: a statement with a `match`; the declaration has its own
auxiliary matcher and the standalone elaboration creates another. -/
theorem withMatch (n : Nat) : (match n with | 0 => true | _ + 1 => false) = (n == 0) := by
  cases n <;> rfl

/-- Acceptance A6: a definition, frozen without an `axioms` clause. -/
def plainDefinition : Nat := 3

/-- Acceptance A7: a definition, frozen with an `axioms` clause. -/
def listedDefinition : Nat := 4

/-- Acceptance A8: a theorem that reaches all three axioms of the R-11
ceiling, frozen with every optional clause. -/
theorem excludedMiddle (p : Prop) : p ∨ ¬p := Classical.em p

/-- Acceptance A9: mask `M2`. -/
theorem settlementFixture (n : Nat) : 0 + n = n := Nat.zero_add n

/-- Acceptance A10: mask `none` with a reason. -/
theorem equationalFixture (n : Nat) : n - 0 = n := rfl

/-- Refusal R1, and witness `FREEZE-CE-001`: the error type `ε` occurs only as
an implicit argument of `Except.ok`, so an ascription that never mentions it
leaves an expression hole. -/
theorem exceptPhantom {ε : Type} (n : Nat) : (Except.ok n : Except ε Nat) = Except.ok n := rfl

set_option linter.unusedVariables false in
/-- Witness `FREEZE-CE-001`: a different statement, `Except Unit Nat`, that
the same `#check` text also accepts. -/
theorem exceptUnit {ε : Type} (n : Nat) : (Except.ok n : Except Unit Nat) = Except.ok n := rfl

/-- Refusal R2: `PUnit` written without its level leaves a universe hole. -/
theorem punitRefl : ∀ (p : PUnit.{u}), p = p := fun _ => rfl

/-- Refusal R3: the declaration's own universe parameter is `u`; an ascription
that names it `v` is another statement. -/
theorem punitNamed : ∀ (p : PUnit.{u + 1}), p = p := fun _ => rfl

/-- A function definitionally equal to `List.length` on `List Nat`, under
another name. -/
def myLength (xs : List Nat) : Nat := xs.length

/-- Refusal R4, and witness `FREEZE-CE-002`: stated with `List.length`;
`#check` also accepts it written with `myLength`. -/
theorem lengthCons (xs : List Nat) : List.length (0 :: xs) = List.length xs + 1 := rfl

/-- Refusal R5: a definition whose second argument is an `optParam`. -/
def withDefault (a : Nat) (b : Nat := 3) : Nat := a + b

/-- Refusal R6: the same `match` subject with other patterns. The two
statements apply their matchers to the same arguments; only the matchers'
bodies differ. -/
theorem matchPatterns (n : Nat) : (match n with | 0 => true | _ + 1 => false) = (n == 0) := by
  cases n <;> rfl

/-- Refusals R7 and R8: a theorem that reaches `propext`. -/
theorem andTrue (p : Prop) : (p ∧ True) = p := propext ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Refusal R9: a theorem that reaches no axiom. -/
theorem noAxiom (n : Nat) : n * 0 = 0 := rfl

/-- Refusals R11 to R14: a definition frozen with a malformed mask clause. -/
def maskTarget : Nat := 5

/-- Refusal R15: the declaration annotates the binder of `e`, so its `match`
elaborates with a known discriminant type. Without the annotation, the
`match` is postponed and Lean wraps the result in a `save_info` metadata
annotation, which the declared type does not carry. -/
theorem typedBinder (xs : List (Nat × Bool)) :
    (List.filterMap (fun (e : Nat × Bool) => match e.2 with | true => some e.1 | false => none)
      xs).length ≤ xs.length :=
  List.length_filterMap_le _ _

end Fixture

/-! ## 3. Acceptance controls

Each command is wrapped in a bare `#guard_msgs`, which asserts that it prints
nothing. Each entry is then read back by `rfl` against the record its clauses
wrote; the entry of `Fixture.n` is the constant
`WhatwgTest.Audit.FreezeContract.frozen.WhatwgTest.Audit.FreezeContract.Fixture.n`. -/

-- A1: the declared type itself.
#guard_msgs in
#whatwg_freeze (@Fixture.exact : ∀ (n : Nat), n + 0 = n) axioms []

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.exact =
    { declaration := ``Fixture.exact, axioms := some [], mask := none, anchor := none,
      graph := none, counterexamples := [] } := rfl

-- A2: a renamed binder.
#guard_msgs in
#whatwg_freeze (@Fixture.renamed : ∀ (k : Nat), k + 0 = k) axioms []

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.renamed =
    { declaration := ``Fixture.renamed, axioms := some [], mask := none, anchor := none,
      graph := none, counterexamples := [] } := rfl

-- A3: an implicit argument made explicit.
#guard_msgs in
#whatwg_freeze (@Fixture.implicitMadeExplicit : ∀ (α : Type) (xs : List α), [] ++ xs = xs)
  axioms []

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.implicitMadeExplicit =
    { declaration := ``Fixture.implicitMadeExplicit, axioms := some [], mask := none,
      anchor := none, graph := none, counterexamples := [] } := rfl

-- A4: a `let`.
#guard_msgs in
#whatwg_freeze (@Fixture.withLet : (let x := 2; x + x) = 4) axioms []

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.withLet =
    { declaration := ``Fixture.withLet, axioms := some [], mask := none, anchor := none,
      graph := none, counterexamples := [] } := rfl

-- A5: a `match`.
#guard_msgs in
#whatwg_freeze (@Fixture.withMatch :
  ∀ (n : Nat), (match n with | 0 => true | _ + 1 => false) = (n == 0)) axioms []

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.withMatch =
    { declaration := ``Fixture.withMatch, axioms := some [], mask := none, anchor := none,
      graph := none, counterexamples := [] } := rfl

-- A6: a definition without an `axioms` clause pins no axiom set.
#guard_msgs in
#whatwg_freeze (@Fixture.plainDefinition : Nat)

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.plainDefinition =
    { declaration := ``Fixture.plainDefinition, axioms := none, mask := none,
      anchor := none, graph := none, counterexamples := [] } := rfl

-- A7: a definition with an `axioms` clause pins its set.
#guard_msgs in
#whatwg_freeze (@Fixture.listedDefinition : Nat) axioms []

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.listedDefinition =
    { declaration := ``Fixture.listedDefinition, axioms := some [], mask := none,
      anchor := none, graph := none, counterexamples := [] } := rfl

-- A8: every optional clause, with the axioms written out of order. The entry
-- records the set sorted by `Lean.Name.lt`, and the other clauses as written.
#guard_msgs in
#whatwg_freeze (@Fixture.excludedMiddle : ∀ (p : Prop), p ∨ ¬p)
  axioms [Quot.sound, Classical.choice, propext]
  mask M1
  anchor "op.enqueue-value-with-size"
  graph "FREEZE-FIXTURE-GRAPH"
  counterexamples ["FREEZE-CE-002", "FREEZE-CE-001"]

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.excludedMiddle =
    { declaration := ``Fixture.excludedMiddle,
      axioms := some [``propext, ``Classical.choice, ``Quot.sound],
      mask := some .chunksAndOutcome,
      anchor := some "op.enqueue-value-with-size",
      graph := some "FREEZE-FIXTURE-GRAPH",
      counterexamples := ["FREEZE-CE-002", "FREEZE-CE-001"] } := rfl

-- A9: mask `M2`.
#guard_msgs in
#whatwg_freeze (@Fixture.settlementFixture : ∀ (n : Nat), 0 + n = n) axioms [] mask M2

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.settlementFixture =
    { declaration := ``Fixture.settlementFixture, axioms := some [],
      mask := some .settlementOrder, anchor := none, graph := none,
      counterexamples := [] } := rfl

-- A10: mask `none` with its reason, recorded as written.
#guard_msgs in
#whatwg_freeze (@Fixture.equationalFixture : ∀ (n : Nat), n - 0 = n) axioms []
  mask none "an equational fixture; it states no observation"

example : frozen.WhatwgTest.Audit.FreezeContract.Fixture.equationalFixture =
    { declaration := ``Fixture.equationalFixture, axioms := some [],
      mask := some (.notApplicable "an equational fixture; it states no observation"),
      anchor := none, graph := none, counterexamples := [] } := rfl

/-! ## 4. Refusal controls

Each command is refused with the diagnostic its docstring freezes, and adds no
entry. -/

-- R1: an expression hole. `Except.ok n` alone leaves its error type open.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.exceptPhantom has an expression hole; write every argument
-/
#guard_msgs in
#whatwg_freeze (@Fixture.exceptPhantom : ∀ {ε : Type} (n : Nat), Except.ok n = Except.ok n)
  axioms []

-- R2: a universe hole. `PUnit` alone leaves its level open.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.punitRefl has a universe hole; write every universe level
-/
#guard_msgs in
#whatwg_freeze (@Fixture.punitRefl : ∀ (p : PUnit), p = p) axioms []

-- R3: a universe parameter under another name.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.punitNamed is not the declared one
  ∀ (p : PUnit), p = p
-/
#guard_msgs in
#whatwg_freeze (@Fixture.punitNamed : ∀ (p : PUnit.{v + 1}), p = p) axioms []

-- R4: a definitionally equal statement that names another function.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.lengthCons is not the declared one
  ∀ (xs : List Nat), (0 :: xs).length = xs.length + 1
-/
#guard_msgs in
#whatwg_freeze (@Fixture.lengthCons :
  ∀ (xs : List Nat), Fixture.myLength (0 :: xs) = Fixture.myLength xs + 1) axioms []

-- R5: an omitted `optParam`.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.withDefault is not the declared one
  Nat → optParam Nat 3 → Nat
-/
#guard_msgs in
#whatwg_freeze (@Fixture.withDefault : Nat → Nat → Nat)

-- R6: a `match` whose patterns differ. The auxiliary matchers are compared by
-- their bodies, which differ.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.matchPatterns is not the declared one
  ∀ (n : Nat),
    (match n with
      | 0 => true
      | n.succ => false) =
      (n == 0)
-/
#guard_msgs in
#whatwg_freeze (@Fixture.matchPatterns :
  ∀ (n : Nat), (match n with | 1 => true | _ => false) = (n == 0)) axioms []

-- R7: a theorem without an `axioms` clause.
/--
error: freeze: WhatwgTest.Audit.FreezeContract.Fixture.andTrue is a theorem; its axioms clause is required
-/
#guard_msgs in
#whatwg_freeze (@Fixture.andTrue : ∀ (p : Prop), (p ∧ True) = p)

-- R8: an axiom reached and not listed.
/--
error: freeze: the axioms of WhatwgTest.Audit.FreezeContract.Fixture.andTrue are [propext]; not listed [propext], listed but not reached []
-/
#guard_msgs in
#whatwg_freeze (@Fixture.andTrue : ∀ (p : Prop), (p ∧ True) = p) axioms []

-- R9: an axiom listed and not reached.
/--
error: freeze: the axioms of WhatwgTest.Audit.FreezeContract.Fixture.noAxiom are []; not listed [], listed but not reached [propext]
-/
#guard_msgs in
#whatwg_freeze (@Fixture.noAxiom : ∀ (n : Nat), n * 0 = 0) axioms [propext]

-- R10: a second entry for one declaration in one module. `Fixture.exact` was
-- frozen by A1.
/--
error: freeze: WhatwgTest.Audit.FreezeContract.Fixture.exact is already frozen in this module
-/
#guard_msgs in
#whatwg_freeze (@Fixture.exact : ∀ (n : Nat), n + 0 = n) axioms []

-- R11: an unknown mask word.
/--
error: freeze: the mask clause of WhatwgTest.Audit.FreezeContract.Fixture.maskTarget is not mask M1, mask M2 or mask none "reason"
-/
#guard_msgs in
#whatwg_freeze (@Fixture.maskTarget : Nat) mask M3

-- R12: `M1` with a reason.
/--
error: freeze: the mask clause of WhatwgTest.Audit.FreezeContract.Fixture.maskTarget is not mask M1, mask M2 or mask none "reason"
-/
#guard_msgs in
#whatwg_freeze (@Fixture.maskTarget : Nat) mask M1 "a reason M1 does not take"

-- R13: `none` without a reason.
/--
error: freeze: the mask clause of WhatwgTest.Audit.FreezeContract.Fixture.maskTarget is not mask M1, mask M2 or mask none "reason"
-/
#guard_msgs in
#whatwg_freeze (@Fixture.maskTarget : Nat) mask none

-- R14: `none` with a blank reason.
/--
error: freeze: the mask clause of WhatwgTest.Audit.FreezeContract.Fixture.maskTarget gives an empty reason
-/
#guard_msgs in
#whatwg_freeze (@Fixture.maskTarget : Nat) mask none " "

-- R15: metadata on one side only. `Expr.eqv` compares metadata, and the
-- judgment drops none.
/--
error: freeze: the statement of WhatwgTest.Audit.FreezeContract.Fixture.typedBinder is not the declared one
  ∀ (xs : List (Nat × Bool)),
    (List.filterMap
          (fun e =>
            match e.snd with
            | true => some e.fst
            | false => none)
          xs).length ≤
      xs.length
-/
#guard_msgs in
#whatwg_freeze (@Fixture.typedBinder : ∀ (xs : List (Nat × Bool)),
    (List.filterMap (fun e => match e.2 with | true => some e.1 | false => none)
      xs).length ≤ xs.length)
  axioms [propext]

/-! ## 5. Counterexample witnesses

`FREEZE-CE-001` and `FREEZE-CE-002` of `test/counterexamples/REGISTER.md`.
Each `#check` below elaborates today, and its output is pinned; refusals R1 and
R4 above are the repair. `FREEZE-CE-003`'s repair is refusals R8 and R9. -/

section Witnesses
set_option linter.unusedVariables false

-- FREEZE-CE-001: one ascription text, two different declared statements, both
-- accepted by `#check`, which fills the hole by unification.
/--
info: @Fixture.exceptPhantom : ∀ {ε : Type} (n : Nat), Except.ok n = Except.ok n
-/
#guard_msgs in
#check (@Fixture.exceptPhantom : ∀ {ε : Type} (n : Nat), Except.ok n = Except.ok n)

/--
info: @Fixture.exceptUnit : ∀ {ε : Type} (n : Nat), Except.ok n = Except.ok n
-/
#guard_msgs in
#check (@Fixture.exceptUnit : ∀ {ε : Type} (n : Nat), Except.ok n = Except.ok n)

-- FREEZE-CE-002: `#check` accepts the statement written with another function,
-- because it unifies at default transparency and unfolds `myLength`.
/--
info: Fixture.lengthCons : ∀ (xs : List Nat), (0 :: xs).length = xs.length + 1
-/
#guard_msgs in
#check (@Fixture.lengthCons :
  ∀ (xs : List Nat), Fixture.myLength (0 :: xs) = Fixture.myLength xs + 1)

end Witnesses

end WhatwgTest.Audit.FreezeContract
