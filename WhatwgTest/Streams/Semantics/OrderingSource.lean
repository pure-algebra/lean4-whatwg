import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q4 battery for the CFG-WPT source/certificate seam.

Contract: `test/contracts/configuration-ordering.contract.md`, §6 as amended by
the "Q4 amendment" section of the same file.
Graph: `CONFIGURATION-PG-ORDERING`, obligation CFG-WPT.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

**Q4 amendment A5, 2026-09-07, breaker seat, branch `promise/q4-amend`.** The
whole of this file is amended. The frozen version at `promise/q4-breaker`
`9ae662a` carried 28 ascriptions: eleven named types with no constructors, four
Props with no checker and no defining equation, three total functions, and two
laws. The Q4 builder recorded in §11.4 of the contract that it was **not
attempted**, and the record is right: nothing above pinned a carrier, so a
builder had no statement to implement and no way to be refused for implementing
the wrong one. Sixty-six of this module's seventy-four diagnostics survived the
first builder pass for that reason.

This amendment makes the seam implementable. Every ascription below is a total
first-order definition, or a `Prop` that is a named `Bool` checker's `= true`,
under `Whatwg.Streams.Semantics.Ordering.Source`. Nothing here carries a
mutable promise table, a scheduler, or a `Config` field; nothing shares a cell
with the runtime; the dependency direction of `docs/ARCHITECTURE.md` is
unchanged; and `WhatwgTest/Streams/Semantics/OrderingBridgeProofs.lean` stays
builder-owned and outside this battery's edit fence (§6.1, ruling R-P21).

**What moved to P8.** `run_erases_to_reference`, the existence half of the
configuration bridge, is **removed from this battery**. Two reasons, both
recorded in the contract's Q4 amendment section: as frozen it is *false*, not
merely hard — it quantifies over an arbitrary start configuration, and
`Reaches c [] c` for a `c` whose trace was fabricated has no causal reference
trace — and even with the missing `c = Semantics.Ordering.initial …`
hypothesis its proof needs `WellFormed` initialization and preservation
(CFG-CELLS, CFG-STACK), the token/mailbox correspondence (CFG-TOKENS), the
ordered-effect receipts (CFG-EFFECTS), the successful-profile progress theorem
and the finite witness through the original start gate. §3.3 of this contract
lists every one of those as still required and this packet states none of them.
What stays here is the half that is about the erasure and is provable from it:
`erasure_preserves_selected_order` on the reference side and
`erases_prefix_selected_order` on the target side.

**What no first-order definition can supply**, also split to P8: the agreement
of the digests below with the sealed bytes of
`vendor/wpt-480fdfcd/streams/writable-streams/reentrant-strategy.any.js` (a
gate in the shape of `lake exe vendorseal`, plus the recorded human
transcription review — a Lean definition cannot read `vendor/`), and the
numeric chunk values of the asserted array (`Semantics.Ordering.Decision α ε`
is polymorphic in the chunk type, so no first-order predicate over it can say
"the chunk is 2"; this battery compares role-and-identity sequences under an
explicit binding, and the numeric agreement is the later host replay under a
named local profile).

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
expected event array is an input to any checker below.

85 ascriptions. The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

/-! ## §A The pinned block and its twelve source occurrences

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

/-! The pinned byte interval of each occurrence role, as an authored total
table; §6.2 of the contract carries the twelve intervals. Ends are exclusive
and offsets are into the whole WPT file, as everywhere in this repository. -/
#check (@Semantics.Ordering.Source.occurrenceSpan :
  Semantics.Ordering.Source.OccurrenceRole → Nat × Nat)

/-! **Amendment A5, addition.** The SHA-256 of each occurrence's exact UTF-8
bytes, as an authored total table, and the block's own span and digest. These
are *data*, not a proof: they are the input to the transcription gate P8 owes,
because a Lean definition cannot read `vendor/`. Freezing them here is what
lets that gate be written against a named constant instead of a re-transcribed
literal. -/
#check (@Semantics.Ordering.Source.occurrenceDigest :
  Semantics.Ordering.Source.OccurrenceRole → String)
#check (@Semantics.Ordering.Source.blockSpan : Nat × Nat)
#check (@Semantics.Ordering.Source.blockDigest : String)

/-! ## §B Return classification

Whether the callback at an occurrence returns a primitive or a promise. The
prefix restriction must not classify every WPT callback as primitive: the flush
callback returns a promise, and the certificate records that. -/

#check (@Semantics.Ordering.Source.ReturnProfile : Type)
#check (@Semantics.Ordering.Source.ReturnProfile.primitive :
  Semantics.Ordering.Source.ReturnProfile)
#check (@Semantics.Ordering.Source.ReturnProfile.promise :
  Semantics.Ordering.Source.ReturnProfile)

/-! ## §C The finite first-order boundary script

**Amendment A5, addition.** The draft names "the fixed original
constructor/start/write script, size callback capture and nested-write /
registration actions" but gives it no carrier, so `SourceProfileCompatible` had
nothing to be checked against. This is that carrier: the pinned block's actions
as data, in source order, with no callback body and no host object. A source
symbol is a fresh `Nat` naming a source-level result (`W0`, `W1`, `W2`, `D0`,
`D1`, `D2`, `F`, `A` of §6.2); it is never a runtime address, and the two are
related only by a `Binding` (§E). -/

#check (@Semantics.Ordering.Source.Symbol : Type)

#check (@Semantics.Ordering.Source.ScriptAction : Type)
#check (@Semantics.Ordering.Source.ScriptAction.construct :
  Semantics.Ordering.Source.ScriptAction)
#check (@Semantics.Ordering.Source.ScriptAction.acquireWriter :
  Semantics.Ordering.Source.ScriptAction)
#check (@Semantics.Ordering.Source.ScriptAction.write :
  Semantics.Ordering.Source.OccurrenceRole → Semantics.Ordering.Source.Symbol →
    Semantics.Ordering.Source.ScriptAction)
#check (@Semantics.Ordering.Source.ScriptAction.attach :
  Nat → Semantics.Ordering.Source.ScriptAction)
#check (@Semantics.Ordering.Source.ScriptAction.callbackReturn :
  Semantics.Ordering.Source.OccurrenceRole → Semantics.Ordering.Source.ReturnProfile →
    Semantics.Ordering.Source.ScriptAction)
#check (@Semantics.Ordering.Source.ScriptAction.scriptReturn :
  Semantics.Ordering.Source.ScriptAction)

/-! The pinned script of the selected case, as one authored constant. It is the
only script this packet admits, and `SourceProfileCompatible` is checked
against `Certificate.script`, never against this name directly, so a later
packet can pin a second case without amending the judgment. -/
#check (@Semantics.Ordering.Source.wptScript :
  List Semantics.Ordering.Source.ScriptAction)

/-! ## §D The source-occurrence, binding and use certificate

**Amendment A5, tightening T1.** `Attachment` and `Certificate` were ascribed
as bare types. A type with no constructor freezes nothing: the builder could
have satisfied both with `Unit`. The constructors below are the freeze. The
`Attachment` fields are exactly the draft's five-tuple
`(receiver, handler, derivedResult, occurrence, capture)`, reordered so that
the occurrence leads, and the `Certificate` components are exactly the four its
frozen docstring names: the script, the attachment list, the return
classifications and the selected-log occurrences. -/

#check (@Semantics.Ordering.Source.Attachment : Type)
#check (@Semantics.Ordering.Source.Attachment.mk :
  Semantics.Ordering.Source.OccurrenceRole → Semantics.Ordering.Source.Symbol →
    Semantics.Ordering.Source.Symbol → Semantics.Ordering.Source.Symbol →
    Option Semantics.Ordering.Source.Symbol → Semantics.Ordering.Source.Attachment)

#check (@Semantics.Ordering.Source.Certificate : Type)
#check (@Semantics.Ordering.Source.Certificate.mk :
  List Semantics.Ordering.Source.ScriptAction → List Semantics.Ordering.Source.Attachment →
    List (Semantics.Ordering.Source.Symbol × Semantics.Ordering.Source.ReturnProfile) →
    List Nat → Semantics.Ordering.Source.Certificate)
#check (@Semantics.Ordering.Source.Certificate.script :
  Semantics.Ordering.Source.Certificate → List Semantics.Ordering.Source.ScriptAction)
#check (@Semantics.Ordering.Source.Certificate.attachments :
  Semantics.Ordering.Source.Certificate → List Semantics.Ordering.Source.Attachment)
#check (@Semantics.Ordering.Source.Certificate.returns :
  Semantics.Ordering.Source.Certificate →
    List (Semantics.Ordering.Source.Symbol × Semantics.Ordering.Source.ReturnProfile))
#check (@Semantics.Ordering.Source.Certificate.selected :
  Semantics.Ordering.Source.Certificate → List Nat)

/-! ## §E The symbol-to-address binding

**Amendment A5, tightening T2.** The draft requires that "runtime references
must be related to the actual returned writer cells through an explicit
symbol-to-address binding witness", and the frozen
`SourceProfileCompatible : Certificate → List (Decision α ε) → Prop` had
nowhere to put it — it would have had to invent the correspondence between
source symbols and runtime cells, which is exactly the confusion the seam
exists to prevent. The binding is a separate argument, never a certificate
component: the certificate is source-only and must stay checkable without any
run. Its two tables are the write-result symbols to write-request identities
and the attachment indices to registration identities. -/

#check (@Semantics.Ordering.Source.Binding : Type)
#check (@Semantics.Ordering.Source.Binding.mk :
  List (Semantics.Ordering.Source.Symbol × Nat) → List (Nat × Nat) →
    Semantics.Ordering.Source.Binding)

/-! ## §F The certificate checker

**Amendment A5, tightening T1.** `SourceChecked` was an unconstrained `Prop`;
`True` satisfied it. It is now a named total decision procedure and the `Prop`
is its `= true`, with the tie frozen as an equation so the builder cannot
widen either half. §6 of the contract carries the conjunct list `sourceCheck`
must decide: the occurrence roles present exactly once each with spans equal to
`occurrenceSpan`; every attachment index in the script in range; fresh derived
result symbols (`Nodup`, and disjoint from the writer results); one return
classification per derived result; the selected indices in range and their
attachments' returns primitive; `D0` and `D1` used by no attachment; the flush
attachment's receiver the outer observer's derived result; and the flush
return classified `promise`. It is checked against source occurrences and use
edges alone: the expected event array is not an argument to it, and neither is
a runtime decision tape or a configuration trace. -/

#check (@Semantics.Ordering.Source.sourceCheck :
  Semantics.Ordering.Source.Certificate → Bool)
#check (@Semantics.Ordering.Source.SourceChecked :
  Semantics.Ordering.Source.Certificate → Prop)
#check (@Semantics.Ordering.Source.sourceChecked_iff :
  ∀ certificate : Semantics.Ordering.Source.Certificate,
    Semantics.Ordering.Source.SourceChecked certificate ↔
      Semantics.Ordering.Source.sourceCheck certificate = true)

/-! ## §G The reference alphabet

**Amendment A5, tightening T3.** `selectedLogs` returned `List OccurrenceRole`.
A role sequence cannot tell `size, 2` from `size, 0`, nor the nested observer
log from the outer one, so the comparison was blind in exactly the place the
WPT array discriminates and the whole obligation would have been satisfiable by
a mutant. `SelectedLog` carries the first-order identity the event already
has — the size call, the sink write request, the registration — and the numeric
chunk values stay outside the model (they are the host replay P8 owes). -/

#check (@Semantics.Ordering.Source.SelectedLog : Type)
#check (@Semantics.Ordering.Source.SelectedLog.size :
  Nat → Semantics.Ordering.Source.SelectedLog)
#check (@Semantics.Ordering.Source.SelectedLog.sink :
  Nat → Semantics.Ordering.Source.SelectedLog)
#check (@Semantics.Ordering.Source.SelectedLog.observer :
  Nat → Semantics.Ordering.Source.SelectedLog)

/-! The immutable reference-trace alphabet: attachment, return, settlement, the
three FIFO events, the selected log, and the original script's return. A
reaction identity is the index of the attachment whose callback it runs, which
is fresh because attachment indices are. There is no promise table here, no
queue object and no callback body. -/

#check (@Semantics.Ordering.Source.ReferenceEvent : Type)
#check (@Semantics.Ordering.Source.ReferenceEvent.attached :
  Nat → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.returned :
  Nat → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.settled :
  Semantics.Ordering.Source.Symbol → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.enqueued :
  Nat → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.started :
  Nat → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.finished :
  Nat → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.logged :
  Semantics.Ordering.Source.SelectedLog → Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.ReferenceEvent.scriptReturned :
  Semantics.Ordering.Source.ReferenceEvent)

/-! ## §H The reference judgment

`CausalPrefix` is a judgment over immutable reference-trace positions. It never
calls `Semantics.Ordering.tick` and never accepts `Semantics.Ordering.Reaches`
as an oracle, and it is not another mutable promise table or a second
executable scheduler. §6 of the contract carries the conjunct list
`causalCheck` must decide, over event positions alone:

1. every `.attached i`, `.returned i`, `.enqueued i`, `.started i`,
   `.finished i` has `i` a valid attachment index of the certificate, and each
   occurs at most once per index;
2. for each index the order is `attached` before `enqueued` before `started`
   before `finished`, each occurrence earlier than the next;
3. immediately before each `.started k`, `k` is the earliest enqueued index
   whose start has not occurred — the fixed single-script FIFO profile;
4. run to completion: between `.started k` and its `.finished k` there is no
   other `.started`; nested size and sink calls are synchronous events inside
   the same episode, not new starts;
5. a live prefix may end with one started but unfinished index and may retain
   enqueued indices that never started; no end is fabricated;
6. attachment to a receiver already settled contributes its `.enqueued` at the
   attachment position, and otherwise the receiver's later `.settled`
   contributes it, in attachment order;
7. a derived-result handler's `.started` follows its producer's `.returned` and
   the `.settled` of the result it derives;
8. every `.logged` event lies inside the episode of an attachment the
   certificate selects, or before `.scriptReturned`, which is where the size
   and sink logs of the original script and its intrinsic calls lie;
9. no `.started` occurs before `.scriptReturned`.

`RetainedFifo` is clauses 1 to 5 alone. It is the part that must survive the
erasure, and it is weaker than `CausalPrefix` precisely because the erased
trace no longer mentions every attachment the certificate has. -/

#check (@Semantics.Ordering.Source.causalCheck :
  Semantics.Ordering.Source.Certificate → List Semantics.Ordering.Source.ReferenceEvent → Bool)
#check (@Semantics.Ordering.Source.CausalPrefix :
  Semantics.Ordering.Source.Certificate → List Semantics.Ordering.Source.ReferenceEvent → Prop)
#check (@Semantics.Ordering.Source.causalPrefix_iff :
  ∀ (certificate : Semantics.Ordering.Source.Certificate)
    (reference : List Semantics.Ordering.Source.ReferenceEvent),
    Semantics.Ordering.Source.CausalPrefix certificate reference ↔
      Semantics.Ordering.Source.causalCheck certificate reference = true)

#check (@Semantics.Ordering.Source.retainedFifo :
  List Semantics.Ordering.Source.ReferenceEvent → Bool)
#check (@Semantics.Ordering.Source.RetainedFifo :
  List Semantics.Ordering.Source.ReferenceEvent → Prop)
#check (@Semantics.Ordering.Source.retainedFifo_iff :
  ∀ reference : List Semantics.Ordering.Source.ReferenceEvent,
    Semantics.Ordering.Source.RetainedFifo reference ↔
      Semantics.Ordering.Source.retainedFifo reference = true)

/-! ## §I The erasure and its property

The erasure map is total: it keeps the selected attachments' events, the writer
results' settlements and every `.logged` event, and it deletes the unselected
attachments (`flushAttachment`, `assertionCall`), the derived results'
settlements, and the enqueue those settlements contribute — which at the prefix
boundary is exactly the pending flush token the draft insists be erased
explicitly. -/

#check (@Semantics.Ordering.Source.referenceErase :
  Semantics.Ordering.Source.Certificate → List Semantics.Ordering.Source.ReferenceEvent →
    List Semantics.Ordering.Source.ReferenceEvent)

/-! **Amendment A5, tightening T7.** The frozen
`referenceSelectedLogs : Certificate → List ReferenceEvent → List SelectedLog`
took a certificate it could not use once the log alphabet carries its own
identity. Selection is decided where it is checkable: clause 8 of
`causalCheck`. This is now the plain projection. -/
#check (@Semantics.Ordering.Source.referenceSelectedLogs :
  List Semantics.Ordering.Source.ReferenceEvent → List Semantics.Ordering.Source.SelectedLog)

/-! **Amendment A5, tightening T4.** The frozen
`erasure_preserves_selected_order` took a target trace and an `ErasesPrefix`
premise and concluded that the two sides' selected logs agree — which under any
honest definition of `ErasesPrefix` is that relation restated, and which is the
vacuous reading §6.2 forbids. The content the draft asks for is about the
erasure map alone: "it must show from the certificate that none of the deleted
events enqueues a retained reaction", and "prove that erasing this internal
work leaves the retained FIFO reaction prefix in order under the fixed profile,
rather than adding that conclusion as a premise". So the law is restated on the
reference side, with no target and no `α`, `ε`:

- the first conjunct is the content. It fails if the certificate does not rule
  out a selected handler on `D0`, because then a deleted derived-result
  settlement enqueues a retained reaction and the retained FIFO breaks;
- the second conjunct is the anti-degeneracy guard on `referenceErase`: an
  erasure that returned `[]`, or that dropped a selected attachment's log,
  would satisfy the first conjunct and fail this one.

Neither premise is the expected WPT array, and the array is not a premise. -/
#check (@Semantics.Ordering.Source.erasure_preserves_selected_order :
  ∀ (certificate : Semantics.Ordering.Source.Certificate)
    (reference : List Semantics.Ordering.Source.ReferenceEvent),
    Semantics.Ordering.Source.SourceChecked certificate →
    Semantics.Ordering.Source.CausalPrefix certificate reference →
      Semantics.Ordering.Source.RetainedFifo
          (Semantics.Ordering.Source.referenceErase certificate reference) ∧
        Semantics.Ordering.Source.referenceSelectedLogs
            (Semantics.Ordering.Source.referenceErase certificate reference) =
          Semantics.Ordering.Source.referenceSelectedLogs reference)

/-! ## §J The target side

`selectedLogs` is the selected-log projection of a configuration trace and
`targetProject` its projection into the reference alphabet; neither is DB-04
M2, and `observeWptOrdering` (decision 4) stays the separate diagnostic.
`bindReference` renames a reference trace's source symbols and attachment
indices to runtime identities through the binding, which is the only place the
two vocabularies meet. -/

#check (@Semantics.Ordering.Source.selectedLogs :
  ∀ {α ε : Type}, List (Semantics.Ordering.Event α ε) →
    List Semantics.Ordering.Source.SelectedLog)

#check (@Semantics.Ordering.Source.targetProject :
  ∀ {α ε : Type}, List (Semantics.Ordering.Event α ε) →
    List Semantics.Ordering.Source.ReferenceEvent)

#check (@Semantics.Ordering.Source.bindReference :
  Semantics.Ordering.Source.Binding → List Semantics.Ordering.Source.ReferenceEvent →
    List Semantics.Ordering.Source.ReferenceEvent)

/-! **Amendment A5, tightening T6.** `ErasesPrefix` was an unconstrained `Prop`
that `True` satisfied, and it took no binding, so it could not have related a
source-symbol trace to a runtime one at all. It is now the equality of the
bound erased reference trace with the target's projection, which is total and
decidable, and the anti-vacuity weight sits where it belongs: on
`CausalPrefix`, which the reference must independently satisfy. Producing a
witness by projecting the target and calling it the reference is refused by
that judgment, not by this one. -/
#check (@Semantics.Ordering.Source.ErasesPrefix :
  ∀ {α ε : Type}, Semantics.Ordering.Source.Certificate →
    Semantics.Ordering.Source.Binding →
    List Semantics.Ordering.Source.ReferenceEvent →
    List (Semantics.Ordering.Event α ε) → Prop)

#check (@Semantics.Ordering.Source.erasesPrefix_iff :
  ∀ {α ε : Type} (certificate : Semantics.Ordering.Source.Certificate)
    (binding : Semantics.Ordering.Source.Binding)
    (reference : List Semantics.Ordering.Source.ReferenceEvent)
    (target : List (Semantics.Ordering.Event α ε)),
    Semantics.Ordering.Source.ErasesPrefix certificate binding reference target ↔
      Semantics.Ordering.Source.bindReference binding
          (Semantics.Ordering.Source.referenceErase certificate reference) =
        Semantics.Ordering.Source.targetProject target)

/-! `SourceProfileCompatible` is checked against the consumed external decision
word and the explicit binding, never against the expected output array and
never against `Semantics.Ordering.Reaches`. It compares the decision word with
`Certificate.script` on decision kind and identity under the binding: the
numeric chunk values are not modelled, for the reason the module docstring
gives. Generic well-formed scripts, different writes, queries or observer
bodies do not qualify merely because they use the same initializer. -/
#check (@Semantics.Ordering.Source.profileCheck :
  ∀ {α ε : Type}, Semantics.Ordering.Source.Certificate →
    Semantics.Ordering.Source.Binding → List (Semantics.Ordering.Decision α ε) → Bool)

#check (@Semantics.Ordering.Source.SourceProfileCompatible :
  ∀ {α ε : Type}, Semantics.Ordering.Source.Certificate →
    Semantics.Ordering.Source.Binding → List (Semantics.Ordering.Decision α ε) → Prop)

#check (@Semantics.Ordering.Source.sourceProfileCompatible_iff :
  ∀ {α ε : Type} (certificate : Semantics.Ordering.Source.Certificate)
    (binding : Semantics.Ordering.Source.Binding)
    (word : List (Semantics.Ordering.Decision α ε)),
    Semantics.Ordering.Source.SourceProfileCompatible certificate binding word ↔
      Semantics.Ordering.Source.profileCheck certificate binding word = true)

/-! ## §K The relation to the selected WPT prefix, and non-vacuity

**Amendment A5, addition.** The pinned certificate and the pinned reference
prefix, as authored constants, with three receipts. `wptSelectedPrefix` is the
selected-log prefix of the asserted array of §3.1, transcribed as data; it is a
**report**, not a check — no checker above takes it as an argument, and the
third receipt only says what the reference produces. The prefix ends after the
outer observer's reaction finishes and before the flush handler starts, so it
covers the whole asserted array; the flush and assertion attachments and the
derived results' settlements are the events `referenceErase` deletes. -/

#check (@Semantics.Ordering.Source.wptCertificate :
  Semantics.Ordering.Source.Certificate)
#check (@Semantics.Ordering.Source.wptReference :
  List Semantics.Ordering.Source.ReferenceEvent)
#check (@Semantics.Ordering.Source.wptSelectedPrefix :
  List Semantics.Ordering.Source.SelectedLog)

#check (@Semantics.Ordering.Source.wptCertificate_checked :
  Semantics.Ordering.Source.sourceCheck Semantics.Ordering.Source.wptCertificate = true)
#check (@Semantics.Ordering.Source.wptReference_causal :
  Semantics.Ordering.Source.causalCheck Semantics.Ordering.Source.wptCertificate
    Semantics.Ordering.Source.wptReference = true)
#check (@Semantics.Ordering.Source.wptReference_selected :
  Semantics.Ordering.Source.referenceSelectedLogs
      (Semantics.Ordering.Source.referenceErase Semantics.Ordering.Source.wptCertificate
        Semantics.Ordering.Source.wptReference) =
    Semantics.Ordering.Source.wptSelectedPrefix)

/-! ## §L The three certificate mutants

**Amendment A5, addition.** §6.2 lists these as still required and the draft
names all three. A `Bool` checker makes them statable now, and without them
`sourceCheck = fun _ => true` passes every receipt above. Each is a certificate
that differs from `wptCertificate` in exactly the way its name says, and each
must be rejected **without consulting the expected WPT output array**, which
`sourceCheck`'s signature enforces. The `WS-CONFIG` register ids are owed at
landing: `test/counterexamples/REGISTER.md` is outside this packet's fence
(contract §9) and no id is frozen here. -/

#check (@Semantics.Ordering.Source.mutantSelectedD0 :
  Semantics.Ordering.Source.Certificate)
#check (@Semantics.Ordering.Source.mutantAliasedResults :
  Semantics.Ordering.Source.Certificate)
#check (@Semantics.Ordering.Source.mutantFlushOnW0 :
  Semantics.Ordering.Source.Certificate)

#check (@Semantics.Ordering.Source.sourceCheck_rejects_selectedD0 :
  Semantics.Ordering.Source.sourceCheck Semantics.Ordering.Source.mutantSelectedD0 = false)
#check (@Semantics.Ordering.Source.sourceCheck_rejects_aliasedResults :
  Semantics.Ordering.Source.sourceCheck Semantics.Ordering.Source.mutantAliasedResults = false)
#check (@Semantics.Ordering.Source.sourceCheck_rejects_flushOnW0 :
  Semantics.Ordering.Source.sourceCheck Semantics.Ordering.Source.mutantFlushOnW0 = false)

/-! ## §M The target-side consequence

The half of the old `run_erases_to_reference` that is about the erasure and is
provable from it: given the witness, the configuration's selected logs are the
reference's, bound. It is short, and it is honest about being short — the WPT
content lives in `SourceChecked`, `CausalPrefix` and
`erasure_preserves_selected_order` above, and in the existence half P8 owes.
Stating it here is what makes `ErasesPrefix` worth having: an `ErasesPrefix`
witness for a source-checked certificate and a causal reference is exactly the
thing from which the ordering conclusion follows. -/
#check (@Semantics.Ordering.Source.erases_prefix_selected_order :
  ∀ {α ε : Type} (certificate : Semantics.Ordering.Source.Certificate)
    (binding : Semantics.Ordering.Source.Binding)
    (reference : List Semantics.Ordering.Source.ReferenceEvent)
    (target : List (Semantics.Ordering.Event α ε)),
    Semantics.Ordering.Source.SourceChecked certificate →
    Semantics.Ordering.Source.CausalPrefix certificate reference →
    Semantics.Ordering.Source.ErasesPrefix certificate binding reference target →
      Semantics.Ordering.Source.selectedLogs target =
        Semantics.Ordering.Source.bindLogs binding
          (Semantics.Ordering.Source.referenceSelectedLogs reference))

/-! The log half of `bindReference`, named separately because the law above is
the only statement that needs it and because a binding that renamed logs one
way and FIFO identities another would be a defect. -/
#check (@Semantics.Ordering.Source.bindLogs :
  Semantics.Ordering.Source.Binding → List Semantics.Ordering.Source.SelectedLog →
    List Semantics.Ordering.Source.SelectedLog)

/-!
Still required and not claimed by this packet, unchanged from the draft except
where the amendment moves an item:

- **P8, the existence half.** `run_erases_to_reference`: for every run of the
  admitted initial configuration whose consumed external decision word is
  `SourceProfileCompatible`, an independently constructed causal reference
  trace and an `ErasesPrefix` witness. Removed from this battery by amendment
  A5; it needs `WellFormed` initialization and preservation, the token/mailbox
  correspondence, the ordered-effect receipts, the successful-profile progress
  theorem and the finite witness through the original start gate, none of which
  this packet states, and as frozen it was false for want of the
  `c = Semantics.Ordering.initial …` hypothesis.
- **P8, the transcription gate.** The agreement of `blockDigest` and
  `occurrenceDigest` with the sealed WPT bytes, and the recorded human
  transcription review. Not a theorem: no first-order definition reads
  `vendor/`.
- **P8, the host replay.** The numeric chunk values of the asserted array,
  under the three local host profiles, by run identifier.
- The `WS-CONFIG` register rows for the three mutants of §L.
-/
