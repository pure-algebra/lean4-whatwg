/-!
# Web IDL exceptions

Owner: the Exceptions section of the pinned Web IDL source, at the part C
surface `PROMISE-PG-FIRST` freezes
(`test/contracts/promise-first-packet.contract.md`). R-P14 makes this its own
sub-slice inside Q3, landed last, after every other move has shown the P4-P7
batteries unchanged.

Landed here: the five simple exception kinds of `op.dfn-simple-exception`
(194433..194721), the 32 base `DOMException` error names in specification
order, and the first-order exception carrier that
`Whatwg.Streams.Boundary.Exception` embeds into (`E-59`, generalize; `G-09`).

**Allocation identity is preserved** (R-P14). Web IDL simple exceptions carry
no identity, but the Streams constructors carry a `Nat` precisely so that two
RangeErrors created by nested size callbacks are distinguishable
(`nested_invalid_sizes_fresh_errors`, `Whatwg/Streams/Readable/Reentrancy.lean`),
so this type keeps the identity and the Web IDL reading is recorded as the
erasure of it. `Exception.simple_eq_iff` and `Exception.domException_eq_iff`
are the receipts.

`E-59` is `generalize`, not `move`: `Whatwg.Streams.Boundary.Exception` keeps
its three constructors and its `deriving DecidableEq, Repr`, so every
`.rangeError id` in the 69 dependent theorems across eight files resolves
unchanged by construction. A `move` would break them, because the general
constructor takes a kind as well as an identity; that is WS-PROM-CE-017.

`QuotaExceededError` is deliberately absent: at this pin it is a derived
interface (`idl.quota-exceeded-error`, 213527..213598), not a base error name,
and the census has no `type.` row for it.

Still open, with their gap ids (`G-09` remainder): `create a DOMException`
(665488..666331), `create a DOMException derived interface` (666333..667324),
`throw an exception` (667326..667543), the six `rule.domexception-derived-*`
rows, `QuotaExceededError` and its serialization steps, and the 25 legacy
`idl.domexception-*-err` code constants.

Strategy question RS-Q3 in `docs/REIFICATION-STRATEGY.md` is answered here:
these are Stratum V data, not a signature.

This module declares no import: it is first-order data over `Nat` and needs
nothing below it (DB-11).
-/

namespace Whatwg.WebIdl.Exceptions

/--
`op.dfn-simple-exception` (194433..194721, digest
`23597069802c1cb8d6b73ddb94125c7fed97b65815cf8e7bf7b3cdd69e1041d3`) lists
exactly five types, one `type.*` row each: `type.eval-error` 194542..194576,
`type.range-error` 194577..194612, `type.reference-error` 194613..194652,
`type.type-error` 194653..194687, `type.uri-error` 194688..194721. Streams
models two of them, so three are added here; §11 of the contract records the
disagreement with `E-59`'s "five of the seven".
-/
inductive Simple where
  | evalError
  | rangeError
  | referenceError
  | typeError
  | uriError
  deriving DecidableEq, Repr

/-- The five kinds, in specification order by ascending byte offset. -/
def Simple.all : List Simple :=
  [Simple.evalError, Simple.rangeError, Simple.referenceError, Simple.typeError,
    Simple.uriError]

/--
The 32 base `DOMException` error names, one `type.*` row each, in
specification order by ascending byte offset, from `type.indexsizeerror` at
200596 to `type.optouterror` at 210922. `G-09`, and R-P10: one definition row
per name, `owned` as data — the table this module reserves, not one
enumeration row.
-/
inductive Name where
  | indexSizeError
  | hierarchyRequestError
  | wrongDocumentError
  | invalidCharacterError
  | noModificationAllowedError
  | notFoundError
  | notSupportedError
  | inUseAttributeError
  | invalidStateError
  | syntaxError
  | invalidModificationError
  | namespaceError
  | invalidAccessError
  | typeMismatchError
  | securityError
  | networkError
  | abortError
  | urlMismatchError
  | timeoutError
  | invalidNodeTypeError
  | dataCloneError
  | encodingError
  | notReadableError
  | unknownError
  | constraintError
  | dataError
  | transactionInactiveError
  | readOnlyError
  | versionError
  | operationError
  | notAllowedError
  | optOutError
  deriving DecidableEq, Repr

/-- The 32 names, in specification order. The gap between `urlMismatchError`
and `timeoutError` is where `QuotaExceededError` used to be. -/
def Name.all : List Name :=
  [Name.indexSizeError, Name.hierarchyRequestError, Name.wrongDocumentError,
    Name.invalidCharacterError, Name.noModificationAllowedError, Name.notFoundError,
    Name.notSupportedError, Name.inUseAttributeError, Name.invalidStateError,
    Name.syntaxError, Name.invalidModificationError, Name.namespaceError,
    Name.invalidAccessError, Name.typeMismatchError, Name.securityError,
    Name.networkError, Name.abortError, Name.urlMismatchError, Name.timeoutError,
    Name.invalidNodeTypeError, Name.dataCloneError, Name.encodingError,
    Name.notReadableError, Name.unknownError, Name.constraintError, Name.dataError,
    Name.transactionInactiveError, Name.readOnlyError, Name.versionError,
    Name.operationError, Name.notAllowedError, Name.optOutError]

/--
`op.dfn-exception` (193998..194431) and `op.js-exception-objects`
(664320..664406): the first-order exception universe. The `Nat` is the model's
allocation identity (R-P14); the `foreign` escape retains a host reason that
carries no model identity.
-/
inductive Exception (reason : Type) where
  | simple (kind : Simple) (id : Nat)
  | domException (name : Name) (id : Nat)
  | foreign (reason : reason)
  deriving DecidableEq, Repr

/-- `op.to-create-a-simple-exception` (664734..665486) at the identity the
consuming calculus allocated. -/
def createSimple {reason : Type} (kind : Simple) (id : Nat) : Exception reason :=
  Exception.simple kind id

/-- The model allocation identity, where there is one. -/
def Exception.identity {reason : Type} : Exception reason → Option Nat
  | .simple _ id => some id
  | .domException _ id => some id
  | .foreign _ => none

/-- The simple-exception classification, where there is one. -/
def Exception.isSimple {reason : Type} : Exception reason → Option Simple
  | .simple kind _ => some kind
  | .domException _ _ => none
  | .foreign _ => none

/-! ## Laws — all mask M1; none observes a settlement order -/

/-- The five `type.*` rows of `op.dfn-simple-exception`. Mask M1. -/
theorem Simple.all_length : Simple.all.length = 5 := rfl

/-- No kind is listed twice. Mask M1. -/
theorem Simple.all_nodup : Simple.all.Nodup := by
  simp [Simple.all]

/-- The table is complete in the other direction. Mask M1. -/
theorem Simple.all_complete (kind : Simple) : kind ∈ Simple.all := by
  cases kind <;> simp [Simple.all]

/-- The 32 base error-name `type.*` rows of the pinned census. Mask M1. -/
theorem Name.all_length : Name.all.length = 32 := rfl

/-- No name is listed twice. Mask M1. -/
theorem Name.all_nodup : Name.all.Nodup := by
  simp [Name.all]

/-- The table is complete in the other direction. Mask M1. -/
theorem Name.all_complete (name : Name) : name ∈ Name.all := by
  cases name <;> simp [Name.all]

/-- `op.to-create-a-simple-exception` builds exactly the tagged exception. Mask M1. -/
theorem createSimple_eq {reason : Type} (kind : Simple) (id : Nat) :
    createSimple (reason := reason) kind id = Exception.simple kind id := rfl

/-- R-P14: distinct allocations remain distinct reasons, exactly as
`Boundary.Exception.rangeError_eq_iff` requires of the Streams type. Mask M1. -/
theorem Exception.simple_eq_iff {reason : Type} (kind : Simple) (left right : Nat) :
    (Exception.simple (reason := reason) kind left = Exception.simple kind right) ↔
      left = right := by
  simp

/-- The same for the `DOMException` names. Mask M1. -/
theorem Exception.domException_eq_iff {reason : Type} (name : Name) (left right : Nat) :
    (Exception.domException (reason := reason) name left =
      Exception.domException name right) ↔ left = right := by
  simp

/-- Mask M1. -/
theorem Exception.identity_simple {reason : Type} (kind : Simple) (id : Nat) :
    Exception.identity (Exception.simple (reason := reason) kind id) = some id := rfl

/-- Mask M1. -/
theorem Exception.identity_domException {reason : Type} (name : Name) (id : Nat) :
    Exception.identity (Exception.domException (reason := reason) name id) = some id := rfl

/-- A foreign reason carries no model allocation identity, exactly as
`Boundary.Exception.toRangeError_foreign` records for the Streams type. Mask M1. -/
theorem Exception.identity_foreign {reason : Type} (r : reason) :
    Exception.identity (Exception.foreign r) = none := rfl

/-- Mask M1. -/
theorem Exception.isSimple_simple {reason : Type} (kind : Simple) (id : Nat) :
    Exception.isSimple (Exception.simple (reason := reason) kind id) = some kind := rfl

/-- A `DOMException` is not a simple exception. Mask M1. -/
theorem Exception.isSimple_domException {reason : Type} (name : Name) (id : Nat) :
    Exception.isSimple (Exception.domException (reason := reason) name id) = none := rfl

/-- A foreign reason is not classified by its host spelling. Mask M1. -/
theorem Exception.isSimple_foreign {reason : Type} (r : reason) :
    Exception.isSimple (Exception.foreign r) = none := rfl

end Whatwg.WebIdl.Exceptions
