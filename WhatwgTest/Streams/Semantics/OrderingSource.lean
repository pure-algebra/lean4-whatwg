import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q4 battery for the CFG-WPT source/certificate seam.

Contract: `test/contracts/configuration-ordering.contract.md`, §6.
Graph: `CONFIGURATION-PG-ORDERING`, obligation CFG-WPT.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

The held draft leaves this surface explicitly unascribed ("source
certificate/reference/checker, WPT diagnostic binding"), and its
coordinator-approved seam splits it three ways: this module owns the
independent source and certificate judgments, a builder-owned
`WhatwgTest/Streams/Semantics/OrderingBridgeProofs.lean` may import them
together with production to prove the configuration bridge, and this module
imports and ascribes those bridge proofs. Neither the source nor the bridge
imports the frozen battery, and production imports no `WhatwgTest` module.

**Amendment to that seam, recorded in §6.1 of the contract.** The draft places
the judgments themselves test-side. A frozen ascription battery cannot both
declare its subject and be the red statement of it, so the judgments are
ascribed here under `Whatwg.Streams.Semantics.Ordering.Source` and authored by
the builder in `Whatwg/Streams/Semantics/`. The reason the seam was drawn is
preserved: the judgment carries no mutable promise table, no scheduler and no
`Config` field, it shares no cell with the runtime, and the dependency
direction of `docs/ARCHITECTURE.md` is unchanged. The alternative — declaring
the judgments in this file — is recorded there as the open decision for the
coordinator.

The judgment is a restricted first-order source profile of one pinned WPT
block. It is not a JavaScript semantics and is not evidence about any host.
Under the authority order of `AGENTS.md` the WPT block supplies an assertion to
replay, never a semantic owner.

Pinned case, unchanged from the draft: WPT commit
`480fdfcd85d043c23875665f464c35c0043dff52`, file
`vendor/wpt-480fdfcd/streams/writable-streams/reentrant-strategy.any.js`,
test `writer.write() promises should resolve in the standard order`, block
`[930, 1956)`, block SHA-256
`386a437a784cb64e46681328c76fe921b755f89f9b64b891bc5ccfc377e3daf5`, file
SHA-256 `f1c493977d45b80e1acd6611dab52896f281d527fe54518d88c39dba200210aa`.
The twelve occurrence intervals and digests are §6.2 of the contract; no
expected event array is an input to the checker.

28 ascriptions. The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

/-! ## The occurrence and attachment data

First-order source data only: byte-interval-anchored occurrence roles, handler
attachments, and return classifications. No callback body is stored, which is
the representation rule of `AGENTS.md`. -/

#check (@Semantics.Ordering.Source.OccurrenceRole : Type)
#check (@Semantics.Ordering.Source.OccurrenceRole.sizeLog :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.positiveGuard :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.nestedWriterCall :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.nestedObserverAttachment :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.sizeReturn :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.writableConstruction :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.sinkLog :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.writerAcquisition :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.outerWriterCall :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.outerObserverAttachment :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.flushAttachment :
  Semantics.Ordering.Source.OccurrenceRole)
#check (@Semantics.Ordering.Source.OccurrenceRole.assertionCall :
  Semantics.Ordering.Source.OccurrenceRole)

/-! The pinned byte interval of each occurrence role, as an authored table.
§6.2 of the contract carries the twelve intervals and their SHA-256 digests. -/
#check (@Semantics.Ordering.Source.occurrenceSpan :
  Semantics.Ordering.Source.OccurrenceRole → Nat × Nat)

/-! Whether the callback at an occurrence returns a primitive or a promise.
The prefix restriction must not classify every WPT callback as primitive: the
flush callback returns a promise, and the certificate records that. -/
#check (@Semantics.Ordering.Source.ReturnProfile : Type)
#check (@Semantics.Ordering.Source.ReturnProfile.primitive :
  Semantics.Ordering.Source.ReturnProfile)
#check (@Semantics.Ordering.Source.ReturnProfile.promise :
  Semantics.Ordering.Source.ReturnProfile)

/-! One `(receiver, handler, derivedResult, occurrence, capture)` row of the
source-use graph. Symbols are fresh source symbols, never runtime addresses. -/
#check (@Semantics.Ordering.Source.Attachment : Type)

/-! The whole certificate: the occurrence roles, the attachment list, the
return classifications and the selected-log occurrences. -/
#check (@Semantics.Ordering.Source.Certificate : Type)

/-! ## The three judgments and the two laws

`SourceChecked` is checked against source occurrences and use edges alone; the
expected event array is not an argument to it. `CausalPrefix` is a judgment
over immutable reference-trace positions and never calls `Config.tick` or
accepts `Config.Reaches` as an oracle. `ErasesPrefix` relates the two traces.
Comparing the erased tape with itself proves no WPT relation, which is why the
reference trace is constructed independently. -/

#check (@Semantics.Ordering.Source.ReferenceEvent : Type)

#check (@Semantics.Ordering.Source.SourceChecked :
  Semantics.Ordering.Source.Certificate → Prop)

#check (@Semantics.Ordering.Source.CausalPrefix :
  Semantics.Ordering.Source.Certificate → List Semantics.Ordering.Source.ReferenceEvent → Prop)

#check (@Semantics.Ordering.Source.ErasesPrefix :
  ∀ {α ε : Type}, Semantics.Ordering.Source.Certificate →
    List Semantics.Ordering.Source.ReferenceEvent →
    List (Semantics.Ordering.Event α ε) → Prop)

#check (@Semantics.Ordering.Source.SourceProfileCompatible :
  ∀ {α ε : Type}, Semantics.Ordering.Source.Certificate →
    List (Semantics.Ordering.Decision α ε) → Prop)

/-! The general certificate law: erasing the unused derived results and the
unselected tail enqueue cannot delete or reorder a selected log before the
prefix boundary. It is proved from the no-handler and boundary conditions,
never assumed, and the expected WPT array is not a premise. -/
#check (@Semantics.Ordering.Source.erasure_preserves_selected_order :
  ∀ {α ε : Type} (certificate : Semantics.Ordering.Source.Certificate)
    (reference : List Semantics.Ordering.Source.ReferenceEvent)
    (target : List (Semantics.Ordering.Event α ε)),
    Semantics.Ordering.Source.SourceChecked certificate →
    Semantics.Ordering.Source.CausalPrefix certificate reference →
    Semantics.Ordering.Source.ErasesPrefix certificate reference target →
      Semantics.Ordering.Source.selectedLogs (α := α) (ε := ε) target =
        Semantics.Ordering.Source.referenceSelectedLogs certificate reference)

/-! The selected-log projection of a configuration trace, and of a reference
trace. These are the two sides the law above equates; neither is DB-04 M2. -/
#check (@Semantics.Ordering.Source.selectedLogs :
  ∀ {α ε : Type}, List (Semantics.Ordering.Event α ε) →
    List Semantics.Ordering.Source.OccurrenceRole)

#check (@Semantics.Ordering.Source.referenceSelectedLogs :
  Semantics.Ordering.Source.Certificate →
    List Semantics.Ordering.Source.ReferenceEvent →
    List Semantics.Ordering.Source.OccurrenceRole)

/-! The configuration bridge, owned by `OrderingBridgeProofs.lean` and ascribed
here: every admitted run whose consumed external word satisfies
`SourceProfileCompatible` and which reaches the post-O2/pre-flush boundary has
an independently constructed causal reference trace and an `ErasesPrefix`
witness. Admitted initialization alone does not restrict later scripts to the
WPT, and proving a list equal to itself satisfies neither half. -/
#check (@Semantics.Ordering.Source.run_erases_to_reference :
  ∀ {α ε : Type} (certificate : Semantics.Ordering.Source.Certificate)
    (c t : Semantics.Ordering.Config α ε)
    (labels : List (Option (Semantics.Ordering.Decision α ε))),
    Semantics.Ordering.Source.SourceChecked certificate →
    Semantics.Ordering.Reaches c labels t →
    Semantics.Ordering.Source.SourceProfileCompatible certificate
        (Semantics.Ordering.externalWord labels) →
      ∃ reference : List Semantics.Ordering.Source.ReferenceEvent,
        Semantics.Ordering.Source.CausalPrefix certificate reference ∧
          Semantics.Ordering.Source.ErasesPrefix certificate reference t.trace)

/-!
Still required, unchanged from the draft: the executable certificate checker,
the three certificate mutants (a selected handler on `D0`, aliased derived
results, a flush that depends on `W0` instead of `D2`), the retained finite
witness through the original start gate, and the later host replay under the
three local profiles. None of those is claimed here.
-/
