import Whatwg.WebIdl

/-!
Breaker-owned Q3 part C battery for `Whatwg.WebIdl.Exceptions`.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, opened in `docs/PROMISE-DAG.md`.

R-P14 makes `Boundary.Exception` (`E-59`, 69 dependent theorems in eight
files) its own sub-slice inside Q3, landed last, after every other move has
shown the P4-P7 batteries unchanged. Allocation identity is preserved: Web IDL
simple exceptions carry none, but the Streams constructors carry a `Nat`
precisely so that two RangeErrors created by nested size callbacks are
distinguishable (`nested_invalid_sizes_fresh_errors`, `Readable/Reentrancy.lean`),
so the general type keeps the identity and the Web IDL reading is recorded as
the erasure of it.

Byte spans are 0-based, ends exclusive, into
`vendor/whatwg-webidl-a652053f/index.bs` (SHA-256
`3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`); row ids
are those of `generated/webidl-census.tsv`. The 32 `Name` constructors are the
32 `type.*` rows of that census that are neither a simple exception nor
`type.idl-promise` / `type.idl-dom-exception`; the contract carries the row id,
span and digest of each. `QuotaExceededError` is deliberately absent: at this
pin it is a derived interface (`idl.quota-exceeded-error`, 213527..213598), not
a base error name, and the census has no `type.` row for it.

Masks (DB-04): every law here is **M1**; none observes a settlement order.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## The five simple exception kinds

`op.dfn-simple-exception`, 194433..194721, digest
`23597069802c1cb8d6b73ddb94125c7fed97b65815cf8e7bf7b3cdd69e1041d3`, lists
exactly five types, one `type.*` row each: `type.eval-error` 194542..194576,
`type.range-error` 194577..194612, `type.reference-error` 194613..194652,
`type.type-error` 194653..194687, `type.uri-error` 194688..194721. `E-59`
records "five of the seven simple exception kinds" as absent; the pinned bytes
have five kinds in total, of which Streams models two, so three are added here.
The contract records the disagreement. -/

#check (@Whatwg.WebIdl.Exceptions.Simple :
  Type)

#check (@Whatwg.WebIdl.Exceptions.Simple.evalError :
  Whatwg.WebIdl.Exceptions.Simple)

#check (@Whatwg.WebIdl.Exceptions.Simple.rangeError :
  Whatwg.WebIdl.Exceptions.Simple)

#check (@Whatwg.WebIdl.Exceptions.Simple.referenceError :
  Whatwg.WebIdl.Exceptions.Simple)

#check (@Whatwg.WebIdl.Exceptions.Simple.typeError :
  Whatwg.WebIdl.Exceptions.Simple)

#check (@Whatwg.WebIdl.Exceptions.Simple.uriError :
  Whatwg.WebIdl.Exceptions.Simple)

#check (inferInstance :
  DecidableEq Whatwg.WebIdl.Exceptions.Simple)

#check (inferInstance :
  Repr Whatwg.WebIdl.Exceptions.Simple)

#check (@Whatwg.WebIdl.Exceptions.Simple.all :
  List Whatwg.WebIdl.Exceptions.Simple)

/-! ## The base `DOMException` error names

`G-09`, and R-P10: one definition row per name, `owned` as data — the table
`Whatwg.WebIdl.Exceptions` reserves, not one enumeration row. Constructors are
in specification order, by ascending byte offset of their `type.*` row, from
`type.indexsizeerror` at 200596 to `type.optouterror` at 210922. -/

#check (@Whatwg.WebIdl.Exceptions.Name :
  Type)

#check (@Whatwg.WebIdl.Exceptions.Name.indexSizeError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.hierarchyRequestError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.wrongDocumentError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.invalidCharacterError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.noModificationAllowedError :
  Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.notFoundError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.notSupportedError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.inUseAttributeError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.invalidStateError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.syntaxError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.invalidModificationError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.namespaceError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.invalidAccessError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.typeMismatchError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.securityError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.networkError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.abortError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.urlMismatchError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.timeoutError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.invalidNodeTypeError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.dataCloneError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.encodingError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.notReadableError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.unknownError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.constraintError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.dataError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.transactionInactiveError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.readOnlyError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.versionError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.operationError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.notAllowedError : Whatwg.WebIdl.Exceptions.Name)
#check (@Whatwg.WebIdl.Exceptions.Name.optOutError : Whatwg.WebIdl.Exceptions.Name)

#check (inferInstance :
  DecidableEq Whatwg.WebIdl.Exceptions.Name)

#check (inferInstance :
  Repr Whatwg.WebIdl.Exceptions.Name)

#check (@Whatwg.WebIdl.Exceptions.Name.all :
  List Whatwg.WebIdl.Exceptions.Name)

/-! ## The exception carrier

`E-59` (generalize). `Whatwg.Streams.Boundary.Exception` is *not* re-pointed:
its two identity-bearing constructors and its `foreign` escape stay exactly as
`READABLE-PG-DEFAULT` froze them, and the general type is related to it by the
embedding and retraction below, which live in `Whatwg/Streams/Boundary/Exception.lean`
and are ascribed in `WhatwgTest/Streams/PromiseBridge.lean`. A `move` here
would break every `.rangeError id` in the 69 dependent theorems, because the
general constructor takes a kind as well as an identity.
Anchors: `op.dfn-exception`, 193998..194431, digest
`a727aa273727aa630983e9f4f49a017ca2c9c421bdfacd3bea03a45fe964a980`;
`op.js-exception-objects`, 664320..664406, digest
`036d4e370d6f4dc68f7266889421e196ca709b894fc8ae9cfd293ae9eac124e4`;
`op.to-create-a-simple-exception`, 664734..665486, digest
`a685c4154d0f603eb41dfcc0b4cafcb2ffcfc201d1519963d63a1008d36351de`. -/

#check (@Whatwg.WebIdl.Exceptions.Exception :
  Type → Type)

#check (@Whatwg.WebIdl.Exceptions.Exception.simple :
  ∀ {reason : Type}, Whatwg.WebIdl.Exceptions.Simple → Nat →
    Whatwg.WebIdl.Exceptions.Exception reason)

#check (@Whatwg.WebIdl.Exceptions.Exception.domException :
  ∀ {reason : Type}, Whatwg.WebIdl.Exceptions.Name → Nat →
    Whatwg.WebIdl.Exceptions.Exception reason)

#check (@Whatwg.WebIdl.Exceptions.Exception.foreign :
  ∀ {reason : Type}, reason → Whatwg.WebIdl.Exceptions.Exception reason)

#check (inferInstance :
  DecidableEq (Whatwg.WebIdl.Exceptions.Exception Nat))

#check (inferInstance :
  Repr (Whatwg.WebIdl.Exceptions.Exception Nat))

#check (@Whatwg.WebIdl.Exceptions.createSimple :
  ∀ {reason : Type}, Whatwg.WebIdl.Exceptions.Simple → Nat →
    Whatwg.WebIdl.Exceptions.Exception reason)

#check (@Whatwg.WebIdl.Exceptions.Exception.identity :
  ∀ {reason : Type}, Whatwg.WebIdl.Exceptions.Exception reason → Option Nat)

#check (@Whatwg.WebIdl.Exceptions.Exception.isSimple :
  ∀ {reason : Type}, Whatwg.WebIdl.Exceptions.Exception reason →
    Option Whatwg.WebIdl.Exceptions.Simple)

/-! ## Laws — all mask M1

`Simple.all` and `Name.all` make the two census tables checkable: their
lengths are the 5 simple-exception rows and the 32 base error-name rows the
contract lists, and neither may repeat a constructor. -/

#check (@Whatwg.WebIdl.Exceptions.Simple.all_length :
  Whatwg.WebIdl.Exceptions.Simple.all.length = 5)

#check (@Whatwg.WebIdl.Exceptions.Simple.all_nodup :
  Whatwg.WebIdl.Exceptions.Simple.all.Nodup)

#check (@Whatwg.WebIdl.Exceptions.Simple.all_complete :
  ∀ (kind : Whatwg.WebIdl.Exceptions.Simple), kind ∈ Whatwg.WebIdl.Exceptions.Simple.all)

#check (@Whatwg.WebIdl.Exceptions.Name.all_length :
  Whatwg.WebIdl.Exceptions.Name.all.length = 32)

#check (@Whatwg.WebIdl.Exceptions.Name.all_nodup :
  Whatwg.WebIdl.Exceptions.Name.all.Nodup)

#check (@Whatwg.WebIdl.Exceptions.Name.all_complete :
  ∀ (name : Whatwg.WebIdl.Exceptions.Name), name ∈ Whatwg.WebIdl.Exceptions.Name.all)

#check (@Whatwg.WebIdl.Exceptions.createSimple_eq :
  ∀ {reason : Type} (kind : Whatwg.WebIdl.Exceptions.Simple) (id : Nat),
    Whatwg.WebIdl.Exceptions.createSimple (reason := reason) kind id =
      Whatwg.WebIdl.Exceptions.Exception.simple kind id)

/-! R-P14: distinct allocations remain distinct reasons, exactly as
`Boundary.Exception.rangeError_eq_iff` and `typeError_eq_iff` require of the
Streams type. -/
#check (@Whatwg.WebIdl.Exceptions.Exception.simple_eq_iff :
  ∀ {reason : Type} (kind : Whatwg.WebIdl.Exceptions.Simple) (left right : Nat),
    (Whatwg.WebIdl.Exceptions.Exception.simple (reason := reason) kind left =
        Whatwg.WebIdl.Exceptions.Exception.simple kind right) ↔ left = right)

#check (@Whatwg.WebIdl.Exceptions.Exception.domException_eq_iff :
  ∀ {reason : Type} (name : Whatwg.WebIdl.Exceptions.Name) (left right : Nat),
    (Whatwg.WebIdl.Exceptions.Exception.domException (reason := reason) name left =
        Whatwg.WebIdl.Exceptions.Exception.domException name right) ↔ left = right)

#check (@Whatwg.WebIdl.Exceptions.Exception.identity_simple :
  ∀ {reason : Type} (kind : Whatwg.WebIdl.Exceptions.Simple) (id : Nat),
    Whatwg.WebIdl.Exceptions.Exception.identity
      (Whatwg.WebIdl.Exceptions.Exception.simple (reason := reason) kind id) = some id)

#check (@Whatwg.WebIdl.Exceptions.Exception.identity_domException :
  ∀ {reason : Type} (name : Whatwg.WebIdl.Exceptions.Name) (id : Nat),
    Whatwg.WebIdl.Exceptions.Exception.identity
      (Whatwg.WebIdl.Exceptions.Exception.domException (reason := reason) name id) = some id)

/-! A foreign reason is not classified by its host spelling and carries no
model allocation identity, exactly as `Boundary.Exception.toRangeError_foreign`
records for the Streams type. -/
#check (@Whatwg.WebIdl.Exceptions.Exception.identity_foreign :
  ∀ {reason : Type} (r : reason),
    Whatwg.WebIdl.Exceptions.Exception.identity
      (Whatwg.WebIdl.Exceptions.Exception.foreign r) = none)

#check (@Whatwg.WebIdl.Exceptions.Exception.isSimple_simple :
  ∀ {reason : Type} (kind : Whatwg.WebIdl.Exceptions.Simple) (id : Nat),
    Whatwg.WebIdl.Exceptions.Exception.isSimple
      (Whatwg.WebIdl.Exceptions.Exception.simple (reason := reason) kind id) = some kind)

#check (@Whatwg.WebIdl.Exceptions.Exception.isSimple_domException :
  ∀ {reason : Type} (name : Whatwg.WebIdl.Exceptions.Name) (id : Nat),
    Whatwg.WebIdl.Exceptions.Exception.isSimple
      (Whatwg.WebIdl.Exceptions.Exception.domException (reason := reason) name id) = none)

#check (@Whatwg.WebIdl.Exceptions.Exception.isSimple_foreign :
  ∀ {reason : Type} (r : reason),
    Whatwg.WebIdl.Exceptions.Exception.isSimple
      (Whatwg.WebIdl.Exceptions.Exception.foreign r) = none)
