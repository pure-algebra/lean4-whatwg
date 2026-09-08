import Whatwg.Streams.Semantics.Configuration

/-!
# Semantics.Source.lean

Owner: the CFG-WPT source and certificate judgment of slice Q4 — the
independent, first-order description of one pinned WPT block, its causal
reference trace, the erasure of the unselected work, and the relation of the
erased reference to a configuration trace.

Spec anchors: none. Under the authority order of `AGENTS.md` the WPT block
supplies an assertion to replay, never a semantic owner. This module is not a
JavaScript semantics and is not evidence about any host.

Packet: `test/contracts/configuration-ordering.contract.md`, §6 as amended by
its "Q4 amendment" section (A5, ruling R-P26). Battery:
`WhatwgTest/Streams/Semantics/OrderingSource.lean`, 86 ascriptions. Graph
`CONFIGURATION-PG-ORDERING`, obligation CFG-WPT.

The seam's reasons are preserved exactly as ruling R-P21 fixed them: nothing
here carries a mutable promise table, a scheduler, or a `Config` field; nothing
shares a cell with the runtime; the dependency direction of
`docs/ARCHITECTURE.md` is unchanged; and production imports no `WhatwgTest`
module.

**Pinned case.** WPT commit `480fdfcd85d043c23875665f464c35c0043dff52`, file
`vendor/wpt-480fdfcd/streams/writable-streams/reentrant-strategy.any.js`, test
`writer.write() promises should resolve in the standard order`, block
`[930, 1956)`. The block digest, the whole-file digest and the twelve
occurrence digests are authored data below. A Lean definition cannot read
`vendor/`: their agreement with the sealed bytes is the transcription gate P8
owes, in the shape of `lake exe vendorseal`, and these constants are its input,
not its proof.

**What P8 owes, and this module does not claim.** `run_erases_to_reference`,
the existence half of the configuration bridge; the transcription gate above;
the numeric chunk values of the asserted array, which are the later host replay
under a named local profile because `Semantics.Ordering.Decision` is
polymorphic in the chunk type; and the `WS-CONFIG` register rows of the three
mutants.
-/

namespace Whatwg.Streams.Semantics.Ordering.Source

open Whatwg.Streams

/-! ## §A The pinned block and its twelve source occurrences -/

/-- The twelve source occurrences of the pinned block, in source order. Each is
a byte interval of the sealed WPT file, never a callback body: the
representation rule of `AGENTS.md` keeps host closures out of stored content. -/
inductive OccurrenceRole where
  | sizeLog
  | positiveGuard
  | nestedWriterCall
  | nestedObserverAttachment
  | sizeReturn
  | writableConstruction
  | sinkLog
  | writerAcquisition
  | outerWriterCall
  | outerObserverAttachment
  | flushAttachment
  | assertionCall
  deriving DecidableEq, Repr, BEq

/-- The twelve roles in source order, as one authored list. -/
def allRoles : List OccurrenceRole :=
  [.sizeLog, .positiveGuard, .nestedWriterCall, .nestedObserverAttachment, .sizeReturn,
    .writableConstruction, .sinkLog, .writerAcquisition, .outerWriterCall,
    .outerObserverAttachment, .flushAttachment, .assertionCall]

/-- The pinned byte interval of each occurrence role. Ends are exclusive and
offsets are into the whole WPT file, as everywhere in this repository. §3.2 of
the contract carries the same twelve intervals. -/
def occurrenceSpan : OccurrenceRole → Nat × Nat
  | .sizeLog => (1031, 1058)
  | .positiveGuard => (1065, 1079)
  | .nestedWriterCall => (1090, 1113)
  | .nestedObserverAttachment => (1126, 1182)
  | .sizeReturn => (1198, 1211)
  | .writableConstruction => (1236, 1256)
  | .sinkLog => (1282, 1315)
  | .writerAcquisition => (1340, 1364)
  | .outerWriterCall => (1367, 1389)
  | .outerObserverAttachment => (1396, 1444)
  | .flushAttachment => (1451, 1482)
  | .assertionCall => (1511, 1538)

/-- The SHA-256 of each occurrence's exact UTF-8 bytes, as authored data. This
is the input to the transcription gate P8 owes, not a proof: freezing it here
lets that gate be written against a named constant rather than a re-transcribed
literal. -/
def occurrenceDigest : OccurrenceRole → String
  | .sizeLog => "7510676d5a833a66299d473f28840d07637bbab8eb383623a0ec8b363abc85c7"
  | .positiveGuard => "28f40d8a6a6d5bc5760b907223315932de3754fb0ac9236e8b8b2a1bb55bc91a"
  | .nestedWriterCall => "d5d4ed5c09faad7f8a1f676117bbc92681a954f07cc69966956085762ef28302"
  | .nestedObserverAttachment => "b42c3cfa5a231120a2fb9614cd3689950fde3bf68452e74c5dffc973175ff1f5"
  | .sizeReturn => "a8f98f8dcdc7e6daec5678b061ec88802a3710047b176579e46c43fa5c6fdc97"
  | .writableConstruction => "b54f90618780d55c8585d0fe11be4ac0d0804d86ba83d734c672f8c97024d579"
  | .sinkLog => "8e6e971e6fd96183f1b0ad0977113914cffc36d443fb7bbabc78648f62baa02e"
  | .writerAcquisition => "787d79d99c9b5bf496a928aeee67188a283c0bb51b07299e2bfb5dd9a8781df2"
  | .outerWriterCall => "c8246ccfffb442e273546c728cc32d214c09d4a4fa80a1eb2fe1a425154aa2b8"
  | .outerObserverAttachment => "3ca2bf8cd597c7e8ba23bd001d50def47988112b1298088b37ebfb81235b967a"
  | .flushAttachment => "60f507054f8c94a978e2113b5c795a7d1d726e1996c2ebe2014b9bc5a6b4d7d3"
  | .assertionCall => "5614ae2f605f04d2ee884755fcc8dbedbc1dfc1faa849f4fc1da0e5cf2389e8c"

/-- The pinned test block's own byte interval in the sealed WPT file. -/
def blockSpan : Nat × Nat := (930, 1956)

/-- The pinned test block's own SHA-256. -/
def blockDigest : String :=
  "386a437a784cb64e46681328c76fe921b755f89f9b64b891bc5ccfc377e3daf5"

/-! ## §B Return classification -/

/-- Whether the callback at an occurrence returns a primitive or a promise. The
prefix restriction must not classify every WPT callback as primitive: the flush
callback returns a promise, and the certificate records that. -/
inductive ReturnProfile where
  | primitive
  | promise
  deriving DecidableEq, Repr, BEq

/-! ## §C The finite first-order boundary script -/

/-- A source-level result name: `W0`, `W1`, `W2`, `D0`, `D1`, `D2`, `F` and `A`
of §3.2 of the contract. It is never a runtime address; the two vocabularies
meet only at a `Binding`. -/
abbrev Symbol : Type := Nat

/-- One admitted boundary action of the pinned block, in source order, with no
callback body and no host object. -/
inductive ScriptAction where
  | construct
  | acquireWriter
  | write (occurrence : OccurrenceRole) (result : Symbol)
  | attach (index : Nat)
  | callbackReturn (occurrence : OccurrenceRole) (profile : ReturnProfile)
  | scriptReturn
  deriving DecidableEq, Repr, BEq

/-- The pinned script of the selected case, unrolled over the admitted
all-successful profile: one `construct`, one writer acquisition, the outer
write and the two nested writes of the reentrant size callback, the three size
returns, the five attachments in the order the source creates them, and the
script's own return. `SourceProfileCompatible` is checked against
`Certificate.script`, never against this name, so a later packet can pin a
second case without amending the judgment. -/
def wptScript : List ScriptAction :=
  [ .construct
  , .acquireWriter
  , .write .outerWriterCall 2
  , .write .nestedWriterCall 1
  , .write .nestedWriterCall 0
  , .callbackReturn .sizeReturn .primitive
  , .attach 0
  , .callbackReturn .sizeReturn .primitive
  , .attach 1
  , .callbackReturn .sizeReturn .primitive
  , .attach 2
  , .attach 3
  , .attach 4
  , .scriptReturn ]

/-! ## §D The source-occurrence, binding and use certificate -/

/-- One handler attachment: the draft's five-tuple
`(receiver, handler, derivedResult, occurrence, capture)`, reordered so that
the occurrence leads. No body is stored; `handler` is a source-level name. -/
structure Attachment where
  occurrence : OccurrenceRole
  receiver : Symbol
  handler : Symbol
  derivedResult : Symbol
  capture : Option Symbol
  deriving DecidableEq, Repr, BEq

/-- The source certificate: the script, the attachment list, the return
classification of each derived result, and the indices of the attachments whose
episodes the selected log prefix covers. Source-only: no runtime tape, no
configuration trace and no expected event array is a component. -/
structure Certificate where
  script : List ScriptAction
  attachments : List Attachment
  returns : List (Symbol × ReturnProfile)
  selected : List Nat
  deriving DecidableEq, Repr, BEq

/-! ## §E The symbol-to-address binding -/

/-- The explicit symbol-to-address witness the draft's own text requires: the
write-result symbols to write-request identities, and the attachment indices to
registration identities. It is a separate argument, never a certificate
component, because the certificate must stay checkable with no run. -/
structure Binding where
  symbols : List (Symbol × Nat)
  attachments : List (Nat × Nat)
  deriving DecidableEq, Repr, BEq

/-- The bound runtime identity of a source symbol; unbound symbols are their own
image, so a binding that omits a symbol cannot silently rename it. -/
def bindSymbol (b : Binding) (s : Symbol) : Nat :=
  ((b.symbols.find? (fun p => p.1 == s)).map Prod.snd).getD s

/-- The bound runtime registration identity of an attachment index. -/
def bindAttachment (b : Binding) (i : Nat) : Nat :=
  ((b.attachments.find? (fun p => p.1 == i)).map Prod.snd).getD i

/-! ## §F The certificate checker -/

/-- The derived results a certificate allocates, in attachment order. -/
def derivedResults (c : Certificate) : List Symbol :=
  c.attachments.map (fun a => a.derivedResult)

/-- The write results the certificate's script produces, in script order. -/
def writerResults (c : Certificate) : List Symbol :=
  c.script.filterMap (fun a => match a with | .write _ s => some s | _ => none)

/-- The attachment indices the script attaches, in script order. -/
def attachIndices (c : Certificate) : List Nat :=
  c.script.filterMap (fun a => match a with | .attach i => some i | _ => none)

/-- The receiver of one attachment index, or `0` when the index is out of
range; `selectedInRange` is what keeps the default unreachable. -/
def receiverOf (c : Certificate) (i : Nat) : Symbol :=
  ((c.attachments[i]?).map (fun a => a.receiver)).getD 0

/-- No entry of a list of naturals repeats. -/
def nodupNat : List Nat → Bool
  | [] => true
  | a :: r => !r.contains a && nodupNat r

/-- Strictly increasing, as a total decision on a list of naturals. -/
def strictIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => decide (a < b) && strictIncreasing (b :: r)

/-- Conjunct 1 of `sourceCheck`, "each occurrence role present once with its
span equal to `occurrenceSpan`", realized as the property of the pinned table
that a first-order definition can decide: the twelve roles carry twelve
nondegenerate spans, strictly increasing in source order and contained in
`blockSpan`. The agreement of those spans with the sealed bytes is the
transcription gate P8 owes. -/
def spanTableOk : Bool :=
  strictIncreasing (allRoles.flatMap (fun r => [(occurrenceSpan r).1, (occurrenceSpan r).2])) &&
    allRoles.all (fun r =>
      decide (blockSpan.1 ≤ (occurrenceSpan r).1) && decide ((occurrenceSpan r).2 ≤ blockSpan.2))

/-- Conjunct 1b: a `write` action names a writer-call occurrence and an
attachment names an attachment occurrence, so a certificate cannot relabel one
source position as another. -/
def rolesShapeOk (c : Certificate) : Bool :=
  c.script.all (fun a => match a with
    | .write role _ => role == OccurrenceRole.nestedWriterCall ||
        role == OccurrenceRole.outerWriterCall
    | .callbackReturn role _ => role == OccurrenceRole.sizeReturn
    | _ => true) &&
  c.attachments.all (fun a =>
    a.occurrence == OccurrenceRole.nestedObserverAttachment ||
    a.occurrence == OccurrenceRole.outerObserverAttachment ||
    a.occurrence == OccurrenceRole.flushAttachment ||
    a.occurrence == OccurrenceRole.assertionCall)

/-- Conjunct 2: every attachment index the script names is in range, and every
attachment is attached exactly once. -/
def attachIndicesOk (c : Certificate) : Bool :=
  nodupNat (attachIndices c) &&
    decide ((attachIndices c).length = c.attachments.length) &&
    (attachIndices c).all (fun i => decide (i < c.attachments.length))

/-- Conjunct 3: derived result symbols are fresh — distinct from one another and
disjoint from the writer results. -/
def freshDerivedOk (c : Certificate) : Bool :=
  nodupNat (derivedResults c) && nodupNat (writerResults c) &&
    (derivedResults c).all (fun s => !(writerResults c).contains s)

/-- Conjunct 4: exactly one return classification per derived result, in
attachment order. -/
def returnsOk (c : Certificate) : Bool :=
  (c.returns.map Prod.fst) == derivedResults c

/-- The classification of one derived result, `primitive` when unclassified;
`returnsOk` is what keeps the default unreachable. -/
def returnOf (c : Certificate) (s : Symbol) : ReturnProfile :=
  ((c.returns.find? (fun p => p.1 == s)).map Prod.snd).getD ReturnProfile.primitive

/-- Conjunct 5: the selected indices are distinct, in range, and their
attachments' handlers return primitives, so a selected episode cannot itself
depend on a further settlement. -/
def selectedOk (c : Certificate) : Bool :=
  nodupNat c.selected &&
    c.selected.all (fun i => decide (i < c.attachments.length)) &&
    c.selected.all (fun i =>
      returnOf c (((c.attachments[i]?).map (fun a => a.derivedResult)).getD 0) ==
        ReturnProfile.primitive)

/-- Conjunct 6, the draft's "`D0` and `D1` are used by no attachment", in the
generic form the erasure needs: no selected attachment observes a derived
result. It is exactly what makes `referenceErase`'s rule — delete the enqueue a
deleted settlement contributes — agree with deleting a whole attachment index,
and it is what `mutantSelectedD0` violates. -/
def selectedOnWriterResults (c : Certificate) : Bool :=
  c.selected.all (fun i => !(derivedResults c).contains (receiverOf c i))

/-- Conjunct 7: the flush attachment observes the outer observer's derived
result, not a writer result. `mutantFlushOnW0` violates it. -/
def flushReceiverOk (c : Certificate) : Bool :=
  match c.attachments.find? (fun a => a.occurrence == OccurrenceRole.flushAttachment),
      c.attachments.find? (fun a => a.occurrence == OccurrenceRole.outerObserverAttachment) with
  | some flush, some outer => flush.receiver == outer.derivedResult
  | _, _ => false

/-- Conjunct 8: the flush handler is classified as returning a promise, so the
prefix restriction cannot treat it as primitive-returning. -/
def flushReturnOk (c : Certificate) : Bool :=
  match c.attachments.find? (fun a => a.occurrence == OccurrenceRole.flushAttachment) with
  | some flush => returnOf c flush.derivedResult == ReturnProfile.promise
  | none => false

/-- The certificate checker. It is checked against source occurrences and use
edges alone: no runtime decision tape, no configuration trace and no expected
event array is an argument to it. -/
def sourceCheck (c : Certificate) : Bool :=
  spanTableOk && rolesShapeOk c && attachIndicesOk c && freshDerivedOk c &&
    returnsOk c && selectedOk c && selectedOnWriterResults c && flushReceiverOk c &&
    flushReturnOk c

/-- The `Prop` face of `sourceCheck`. -/
def SourceChecked (c : Certificate) : Prop := sourceCheck c = true

/-- The two faces agree by definition, frozen so neither can be widened. -/
theorem sourceChecked_iff (certificate : Certificate) :
    SourceChecked certificate ↔ sourceCheck certificate = true := Iff.rfl

/-! ## §G The reference alphabet -/

/-- One entry of the selected log, carrying the first-order identity the event
already has. The numeric chunk values stay outside the model: they are the host
replay P8 owes. -/
inductive SelectedLog where
  | size (call : Nat)
  | sink (request : Nat)
  | observer (registration : Nat)
  deriving DecidableEq, Repr, BEq

/-- The immutable reference-trace alphabet: attachment, handler return,
settlement, the three FIFO events, the selected log, and the original script's
return. A reaction identity is the index of the attachment whose callback it
runs. There is no promise table here, no queue object and no callback body. -/
inductive ReferenceEvent where
  | attached (index : Nat)
  | returned (index : Nat)
  | settled (result : Symbol)
  | enqueued (index : Nat)
  | started (index : Nat)
  | finished (index : Nat)
  | logged (entry : SelectedLog)
  | scriptReturned
  deriving DecidableEq, Repr, BEq

/-! ## §H The reference judgment -/

/-- The FIFO skeleton of one reference event: its kind code and its attachment
index. `attached 0 < enqueued 1 < started 2 < returned 3 < finished 4` is the
per-index order clause 2 requires. -/
def fifoKind : ReferenceEvent → Option (Nat × Nat)
  | .attached i => some (0, i)
  | .enqueued i => some (1, i)
  | .started i => some (2, i)
  | .returned i => some (3, i)
  | .finished i => some (4, i)
  | _ => none

/-- The FIFO skeleton of a whole reference trace, in trace order. -/
def fifoTrace (evs : List ReferenceEvent) : List (Nat × Nat) := evs.filterMap fifoKind

/-- No `(kind, index)` pair repeats. -/
def nodupPairs : List (Nat × Nat) → Bool
  | [] => true
  | a :: r => !r.contains a && nodupPairs r

/-- Clause 2: for every index, the kinds occur in strictly increasing order. -/
def kindsOk (t : List (Nat × Nat)) : Bool :=
  (t.map Prod.snd).all (fun i =>
    strictIncreasing ((t.filter (fun e => e.2 == i)).map Prod.fst))

/-- Clauses 4 and 5: starts and finishes alternate with matching indices, and a
live prefix may end with one started but unfinished index. -/
def startFinishOk : List (Nat × Nat) → Bool
  | [] => true
  | [e] => e.1 == 2
  | e1 :: e2 :: rest =>
      e1.1 == 2 && e2.1 == 4 && e1.2 == e2.2 && startFinishOk rest

/-- Clauses 1 to 5 over the FIFO skeleton: at most once per kind and index; the
per-index order; the single-script FIFO rule, as "the started indices are a
prefix of the enqueued indices"; run to completion; and the live tail. -/
def fifoOk (t : List (Nat × Nat)) : Bool :=
  nodupPairs t && kindsOk t &&
    ((t.filter (fun e => e.1 == 2)).map Prod.snd).isPrefixOf
      ((t.filter (fun e => e.1 == 1)).map Prod.snd) &&
    startFinishOk (t.filter (fun e => e.1 == 2 || e.1 == 4))

/-- Clauses 1 to 5 alone: the part of the reference judgment that must survive
the erasure. It is weaker than `CausalPrefix` precisely because the erased trace
no longer mentions every attachment the certificate has. -/
def retainedFifo (reference : List ReferenceEvent) : Bool := fifoOk (fifoTrace reference)

/-- The `Prop` face of `retainedFifo`. -/
def RetainedFifo (reference : List ReferenceEvent) : Prop := retainedFifo reference = true

/-- The two faces agree by definition. -/
theorem retainedFifo_iff (reference : List ReferenceEvent) :
    RetainedFifo reference ↔ retainedFifo reference = true := Iff.rfl

/-- The position of an event in a reference trace. -/
def posOf (evs : List ReferenceEvent) (e : ReferenceEvent) : Option Nat :=
  evs.findIdx? (fun x => x == e)

/-- Both events occur, and the first strictly earlier. -/
def before (evs : List ReferenceEvent) (a b : ReferenceEvent) : Bool :=
  match posOf evs a, posOf evs b with
  | some i, some j => decide (i < j)
  | _, _ => false

/-- Clause 1's certificate half: every FIFO index is a valid attachment index. -/
def indexOk (c : Certificate) (evs : List ReferenceEvent) : Bool :=
  (fifoTrace evs).all (fun p => decide (p.2 < c.attachments.length))

/-- Clause 6: an attachment's reaction is enqueued after the attachment itself
and after its receiver settles, and attachments on one receiver are enqueued in
attachment order. -/
def enqueueOk (c : Certificate) (evs : List ReferenceEvent) : Bool :=
  (List.range c.attachments.length).all (fun i =>
    if evs.contains (.enqueued i) then
      before evs (.attached i) (.enqueued i) &&
        before evs (.settled (receiverOf c i)) (.enqueued i)
    else true) &&
  (List.range c.attachments.length).all (fun i =>
    (List.range c.attachments.length).all (fun j =>
      if decide (i < j) && (receiverOf c i == receiverOf c j) &&
          evs.contains (.enqueued i) && evs.contains (.enqueued j) then
        before evs (.enqueued i) (.enqueued j)
      else true))

/-- Clause 7: a derived-result handler starts only after its producer returns
and after the result it derives settles. -/
def derivedStartOk (c : Certificate) (evs : List ReferenceEvent) : Bool :=
  (List.range c.attachments.length).all (fun i =>
    if evs.contains (.started i) then
      match c.attachments.findIdx? (fun b => b.derivedResult == receiverOf c i) with
      | some j =>
          before evs (.returned j) (.started i) &&
            before evs (.settled (receiverOf c i)) (.started i)
      | none => true
    else true)

/-- Clauses 8 and 9, as one left-to-right walk: no episode starts before the
script returns or inside another episode; a finish closes the episode it names;
an observer log lies inside the episode of the selected attachment it names; and
every other log — the size and sink logs of the original script and of its
intrinsic calls — lies outside every episode. -/
def logsOk (c : Certificate) : Bool → Option Nat → List ReferenceEvent → Bool
  | _, _, [] => true
  | scriptDone, running, e :: rest =>
      match e with
      | .scriptReturned => logsOk c true running rest
      | .started k => scriptDone && running.isNone && logsOk c scriptDone (some k) rest
      | .finished k => (running == some k) && logsOk c scriptDone none rest
      | .logged (.observer i) =>
          (running == some i) && c.selected.contains i && logsOk c scriptDone running rest
      | .logged _ => running.isNone && logsOk c scriptDone running rest
      | _ => logsOk c scriptDone running rest

/-- The reference judgment: a judgment over immutable reference-trace positions.
It never calls `Semantics.Ordering.tick`, never accepts
`Semantics.Ordering.Reaches` as an oracle, and is neither a second mutable
promise table nor a second executable scheduler. -/
def causalCheck (c : Certificate) (reference : List ReferenceEvent) : Bool :=
  retainedFifo reference && indexOk c reference && enqueueOk c reference &&
    derivedStartOk c reference && logsOk c false none reference

/-- The `Prop` face of `causalCheck`. -/
def CausalPrefix (c : Certificate) (reference : List ReferenceEvent) : Prop :=
  causalCheck c reference = true

/-- The two faces agree by definition. -/
theorem causalPrefix_iff (certificate : Certificate) (reference : List ReferenceEvent) :
    CausalPrefix certificate reference ↔ causalCheck certificate reference = true := Iff.rfl

/-! ## §I The erasure and its property -/

/-- What the erasure keeps. The FIFO events of a selected attachment stay; the
settlement of a writer result stays; every log stays; and the enqueue a deleted
settlement contributes goes, which at the prefix boundary is exactly the pending
flush token the draft insists be erased explicitly. Conjunct 6 of `sourceCheck`
is what makes the second rule agree with deleting a whole attachment index. -/
def eraseKeep (c : Certificate) : ReferenceEvent → Bool
  | .attached i => c.selected.contains i
  | .returned i => c.selected.contains i
  | .started i => c.selected.contains i
  | .finished i => c.selected.contains i
  | .enqueued i => c.selected.contains i && !(derivedResults c).contains (receiverOf c i)
  | .settled s => !(derivedResults c).contains s
  | .logged _ => true
  | .scriptReturned => true

/-- The erasure map: total, and a filter, so it can delete but never reorder. -/
def referenceErase (c : Certificate) (reference : List ReferenceEvent) :
    List ReferenceEvent :=
  reference.filter (eraseKeep c)

/-- The log an event carries, if any. -/
private def logOf : ReferenceEvent → Option SelectedLog
  | .logged l => some l
  | _ => none

/-- The selected logs of a reference trace, in trace order. Selection is decided
by `logsOk`, where it is checkable; this is the plain projection. -/
def referenceSelectedLogs (reference : List ReferenceEvent) : List SelectedLog :=
  reference.filterMap logOf

/-! ### Filter stability, the content of the erasure law -/

/-- The cons step of `List.filter`, as a plain equation. -/
private theorem filter_cons_eq {A : Type} (p : A → Bool) (a : A) (l : List A) :
    (a :: l).filter p = if p a then a :: l.filter p else l.filter p := List.filter_cons

/-- A `filterMap` after a `filter` is a `filter` after the `filterMap`, whenever
the two predicates agree wherever the map produces a value. -/
private theorem filterMap_filter {A B : Type} (f : A → Option B) (p : A → Bool) (q : B → Bool)
    (h : ∀ a b, f a = some b → p a = q b) :
    ∀ l : List A, (l.filter p).filterMap f = (l.filterMap f).filter q
  | [] => rfl
  | a :: l => by
      have ih := filterMap_filter f p q h l
      cases hfa : f a with
      | none =>
          have hR : ((a :: l).filterMap f) = l.filterMap f := List.filterMap_cons_none hfa
          by_cases hp : p a = true
          · have hL : ((a :: l).filter p) = a :: l.filter p := by
              rw [filter_cons_eq, if_pos hp]
            rw [hL, hR, List.filterMap_cons_none hfa, ih]
          · have hL : ((a :: l).filter p) = l.filter p := by
              rw [filter_cons_eq, if_neg hp]
            rw [hL, hR, ih]
      | some b =>
          have hpq : p a = q b := h a b hfa
          have hR : ((a :: l).filterMap f) = b :: l.filterMap f := List.filterMap_cons_some hfa
          by_cases hp : p a = true
          · have hq : q b = true := hpq ▸ hp
            have hL : ((a :: l).filter p) = a :: l.filter p := by
              rw [filter_cons_eq, if_pos hp]
            rw [hL, hR, List.filterMap_cons_some hfa, ih, filter_cons_eq, if_pos hq]
          · have hq : ¬ (q b = true) := by rw [← hpq]; exact hp
            have hL : ((a :: l).filter p) = l.filter p := by
              rw [filter_cons_eq, if_neg hp]
            rw [hL, hR, ih, filter_cons_eq, if_neg hq]

/-- Mapping after filtering on the image is filtering after mapping. -/
private theorem map_filter_comm {A B : Type} (f : A → B) (q : B → Bool) :
    ∀ l : List A, (l.map f).filter q = (l.filter (fun a => q (f a))).map f
  | [] => rfl
  | a :: l => by
      by_cases h : q (f a) = true <;>
        simp [h, map_filter_comm f q l]

/-- A sublist of a repetition-free list is repetition-free. -/
private theorem nodupPairs_filter (p : (Nat × Nat) → Bool) :
    ∀ t : List (Nat × Nat), nodupPairs t = true → nodupPairs (t.filter p) = true
  | [], _ => rfl
  | a :: t, h => by
      simp only [nodupPairs, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hmem, htail⟩ := h
      by_cases hp : p a = true
      · rw [filter_cons_eq, if_pos hp]
        simp only [nodupPairs, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨?_, nodupPairs_filter p t htail⟩
        cases hcon : (t.filter p).contains a with
        | false => rfl
        | true =>
            exfalso
            have h1 : a ∈ t.filter p := by simpa using hcon
            have h2 : (t.contains a) = true := by simpa using (List.mem_filter.mp h1).1
            rw [hmem] at h2
            exact Bool.noConfusion h2
      · rw [filter_cons_eq, if_neg hp]
        exact nodupPairs_filter p t htail

/-- Clause 2 survives a filter on the attachment index. -/
private theorem kindsOk_filter (q : Nat → Bool) (t : List (Nat × Nat))
    (h : kindsOk t = true) : kindsOk (t.filter (fun e => q e.2)) = true := by
  simp only [kindsOk, List.all_eq_true] at h ⊢
  intro i hi
  obtain ⟨e, he, hei⟩ := List.mem_map.mp hi
  have hqe : q e.2 = true := (List.mem_filter.mp he).2
  have hmem : i ∈ t.map Prod.snd :=
    List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, hei⟩
  have hqi : q i = true := hei ▸ hqe
  have hfilter : (t.filter (fun e => q e.2)).filter (fun e => e.2 == i) =
      t.filter (fun e => e.2 == i) := by
    rw [List.filter_filter]
    refine List.filter_congr ?_
    intro x _
    by_cases hx : x.2 = i
    · simp [hx, hqi]
    · simp [hx]
  rw [hfilter]
  exact h i hmem

/-- Clause 3 survives a filter on the attachment index. -/
private theorem isPrefixOf_filter (q : Nat → Bool) (A B : List Nat)
    (h : A.isPrefixOf B = true) : (A.filter q).isPrefixOf (B.filter q) = true := by
  rw [List.isPrefixOf_iff_prefix] at h ⊢
  obtain ⟨s, hs⟩ := h
  exact ⟨s.filter q, by rw [← List.filter_append, hs]⟩

/-- Clauses 4 and 5 survive a filter on the attachment index: a deleted index
takes its start and its finish together, or a lone trailing start. -/
private theorem startFinishOk_filter (q : Nat → Bool) :
    ∀ s : List (Nat × Nat), startFinishOk s = true →
      startFinishOk (s.filter (fun e => q e.2)) = true
  | [], _ => rfl
  | [e], h => by
      by_cases hq : q e.2 = true
      · rw [filter_cons_eq, if_pos hq, List.filter_nil]
        exact h
      · rw [filter_cons_eq, if_neg hq, List.filter_nil]
        rfl
  | e1 :: e2 :: rest, h => by
      simp only [startFinishOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h12⟩, hrest⟩ := h
      have hq : q e1.2 = q e2.2 := by rw [h12]
      by_cases hk : q e1.2 = true
      · have hk2 : q e2.2 = true := hq ▸ hk
        rw [filter_cons_eq, if_pos hk, filter_cons_eq, if_pos hk2]
        simp only [startFinishOk, Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨⟨h1, h2⟩, h12⟩, startFinishOk_filter q rest hrest⟩
      · have hk2 : ¬ (q e2.2 = true) := by rw [← hq]; exact hk
        rw [filter_cons_eq, if_neg hk, filter_cons_eq, if_neg hk2]
        exact startFinishOk_filter q rest hrest

/-- Clauses 1 to 5 survive a filter on the attachment index. This is the whole
content of `erasure_preserves_selected_order`'s first conjunct. -/
private theorem fifoOk_filter (q : Nat → Bool) (t : List (Nat × Nat)) (h : fifoOk t = true) :
    fifoOk (t.filter (fun e => q e.2)) = true := by
  simp only [fifoOk, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hn, hk⟩, hp⟩, hsf⟩ := h
  refine ⟨⟨⟨nodupPairs_filter _ t hn, kindsOk_filter q t hk⟩, ?_⟩, ?_⟩
  · have hcomm : ∀ (n : Nat),
        ((t.filter (fun e => q e.2)).filter (fun e => e.1 == n)).map Prod.snd =
          (((t.filter (fun e => e.1 == n)).map Prod.snd)).filter q := by
      intro n
      rw [List.filter_filter, map_filter_comm, List.filter_filter]
      refine congrArg (List.map Prod.snd) (List.filter_congr ?_)
      intro x _
      exact Bool.and_comm _ _
    rw [hcomm 2, hcomm 1]
    exact isPrefixOf_filter q _ _ hp
  · have hcomm : (t.filter (fun e => q e.2)).filter (fun e => e.1 == 2 || e.1 == 4) =
        (t.filter (fun e => e.1 == 2 || e.1 == 4)).filter (fun e => q e.2) := by
      rw [List.filter_filter, List.filter_filter]
      refine List.filter_congr ?_
      intro x _
      exact Bool.and_comm _ _
    rw [hcomm]
    exact startFinishOk_filter q _ hsf

/-- The erasure keeps every log, so the selected logs are unchanged. -/
private theorem referenceSelectedLogs_erase (c : Certificate) (reference : List ReferenceEvent) :
    referenceSelectedLogs (referenceErase c reference) = referenceSelectedLogs reference := by
  have h := filterMap_filter logOf
    (eraseKeep c) (fun _ => true) (by
      intro a b hab
      cases a <;> simp_all [eraseKeep, logOf])
    reference
  simp only [referenceSelectedLogs, referenceErase]
  rw [h]
  simp

/-- Under `SourceChecked` the erasure's rule agrees with deleting a whole
attachment index, which is what carries the FIFO clauses across it. -/
private theorem fifoTrace_erase (c : Certificate) (hs : sourceCheck c = true)
    (reference : List ReferenceEvent) :
    fifoTrace (referenceErase c reference) =
      (fifoTrace reference).filter (fun p => c.selected.contains p.2) := by
  have hsel : selectedOnWriterResults c = true := by
    simp only [sourceCheck, Bool.and_eq_true] at hs
    exact hs.1.1.2
  refine filterMap_filter fifoKind (eraseKeep c) (fun p => c.selected.contains p.2) ?_ reference
  intro a b hab
  cases a with
  | attached i =>
      simp only [fifoKind, Option.some.injEq] at hab
      subst hab
      rfl
  | returned i =>
      simp only [fifoKind, Option.some.injEq] at hab
      subst hab
      rfl
  | started i =>
      simp only [fifoKind, Option.some.injEq] at hab
      subst hab
      rfl
  | finished i =>
      simp only [fifoKind, Option.some.injEq] at hab
      subst hab
      rfl
  | enqueued i =>
      simp only [fifoKind, Option.some.injEq] at hab
      subst hab
      simp only [eraseKeep]
      cases hc : c.selected.contains i with
      | false => simp
      | true =>
          simp only [selectedOnWriterResults, List.all_eq_true] at hsel
          have := hsel i (by simpa using hc)
          simp_all
  | settled _ => simp [fifoKind] at hab
  | logged _ => simp [fifoKind] at hab
  | scriptReturned => simp [fifoKind] at hab

/--
The erasure law, on the reference side: from the certificate and the reference
judgment alone, the retained FIFO prefix survives the erasure in order, and no
selected log is lost.

The first conjunct is the content the draft demands — "it must show from the
certificate that none of the deleted events enqueues a retained reaction". It
fails the moment the certificate stops ruling out a selected handler on `D0`:
`selectedOnWriterResults` is the conjunct `fifoTrace_erase` consumes, and
`mutantSelectedD0` is the certificate that violates it. The second conjunct is
the anti-degeneracy guard: an erasure returning `[]`, or one that dropped a
selected attachment's log, would satisfy the first and fail this one.

Neither premise is the expected WPT array, and the array is not a premise.
-/
theorem erasure_preserves_selected_order (certificate : Certificate)
    (reference : List ReferenceEvent) (hs : SourceChecked certificate)
    (hc : CausalPrefix certificate reference) :
    RetainedFifo (referenceErase certificate reference) ∧
      referenceSelectedLogs (referenceErase certificate reference) =
        referenceSelectedLogs reference := by
  refine ⟨?_, referenceSelectedLogs_erase certificate reference⟩
  have hr : retainedFifo reference = true := by
    simp only [CausalPrefix, causalCheck, Bool.and_eq_true] at hc
    exact hc.1.1.1.1
  show fifoOk (fifoTrace (referenceErase certificate reference)) = true
  rw [fifoTrace_erase certificate hs reference]
  exact fifoOk_filter _ _ hr

/-! ## §J The target side -/

/-- The reference-alphabet projection of a configuration trace. Neither this nor
`selectedLogs` is DB-04 M2, and `observeWptOrdering` (decision 4) stays the
separate diagnostic. -/
def targetProject {α ε : Type} (trace : List (Semantics.Ordering.Event α ε)) :
    List ReferenceEvent :=
  trace.filterMap (fun e => match e with
    | .writable (.sizeCalled _ call _) => some (.logged (.size call))
    | .writable (.sinkCalled _ (.write request _)) => some (.logged (.sink request))
    | .writable (.settled request _) => some (.settled request)
    | .writable _ => none
    | .registered registration _ _ => some (.attached registration)
    | .observerCalled registration _ _ _ => some (.logged (.observer registration))
    | .observerReturned registration => some (.returned registration)
    | .jobQueued job => match job.kind with
        | .observer registration => some (.enqueued registration)
        | _ => none
    | .jobStarted job => match job.kind with
        | .observer registration => some (.started registration)
        | _ => none
    | .jobFinished job => match job.kind with
        | .observer registration => some (.finished registration)
        | _ => none
    | .scriptEntered => none
    | .scriptReturned => some .scriptReturned)

/-- The selected logs of a configuration trace. -/
def selectedLogs {α ε : Type} (trace : List (Semantics.Ordering.Event α ε)) :
    List SelectedLog :=
  referenceSelectedLogs (targetProject trace)

/-- One selected log, renamed to runtime identities. -/
def bindLog (b : Binding) : SelectedLog → SelectedLog
  | .size call => .size (bindSymbol b call)
  | .sink request => .sink (bindSymbol b request)
  | .observer registration => .observer (bindAttachment b registration)

/-- The log half of `bindReference`, named separately because
`erases_prefix_selected_order` is the only statement that needs it and because a
binding that renamed logs one way and FIFO identities another would be a
defect. -/
def bindLogs (b : Binding) (logs : List SelectedLog) : List SelectedLog :=
  logs.map (bindLog b)

/-- One reference event, renamed to runtime identities. -/
private def bindEvent (b : Binding) : ReferenceEvent → ReferenceEvent
  | .attached i => .attached (bindAttachment b i)
  | .returned i => .returned (bindAttachment b i)
  | .enqueued i => .enqueued (bindAttachment b i)
  | .started i => .started (bindAttachment b i)
  | .finished i => .finished (bindAttachment b i)
  | .settled s => .settled (bindSymbol b s)
  | .logged l => .logged (bindLog b l)
  | .scriptReturned => .scriptReturned

/-- A reference trace renamed to runtime identities: the only place the source
and runtime vocabularies meet. -/
def bindReference (b : Binding) (reference : List ReferenceEvent) :
    List ReferenceEvent :=
  reference.map (bindEvent b)

/-- The erased reference, bound, is the target's projection. Total and
decidable; the anti-vacuity weight sits on `CausalPrefix`, which the reference
must independently satisfy, so producing a witness by projecting the target and
calling it the reference is refused by that judgment, not by this one. -/
def ErasesPrefix {α ε : Type} (c : Certificate) (b : Binding)
    (reference : List ReferenceEvent) (target : List (Semantics.Ordering.Event α ε)) : Prop :=
  bindReference b (referenceErase c reference) = targetProject target

/-- The relation is that equality, frozen. -/
theorem erasesPrefix_iff {α ε : Type} (certificate : Certificate) (binding : Binding)
    (reference : List ReferenceEvent) (target : List (Semantics.Ordering.Event α ε)) :
    ErasesPrefix certificate binding reference target ↔
      bindReference binding (referenceErase certificate reference) = targetProject target :=
  Iff.rfl

/-- The comparable shape of one script action under the binding. -/
def scriptShape (c : Certificate) (b : Binding) : ScriptAction → Option (Nat × Nat × Nat)
  | .construct => none
  | .acquireWriter => none
  | .write _ _ => some (0, 0, 0)
  | .attach i =>
      (c.attachments[i]?).map (fun a => (1, bindSymbol b a.receiver, bindAttachment b i))
  | .callbackReturn _ _ => some (2, 0, 0)
  | .scriptReturn => some (3, 0, 0)

/-- The comparable shape of one admitted external decision. A decision this
profile does not admit takes the reserved code `9`, so a generic well-formed
script does not qualify merely because it uses the same initializer. -/
def decisionShape {α ε : Type} : Semantics.Ordering.Decision α ε → Option (Nat × Nat × Nat)
  | .writable (.write _) => some (0, 0, 0)
  | .writable (.returnSize _) => some (2, 0, 0)
  | .writable _ => some (9, 0, 0)
  | .observe p callback => some (1, p.cell, callback)
  | .observerReturn => some (2, 0, 0)
  | .scriptReturn => some (3, 0, 0)
  | .scriptBegin => none

/-- The consumed external decision word compared with `Certificate.script` on
decision kind and identity under the binding, never against the expected output
array and never against `Semantics.Ordering.Reaches`. The numeric chunk values
are not modelled, for the reason the module docstring gives. -/
def profileCheck {α ε : Type} (c : Certificate) (b : Binding)
    (word : List (Semantics.Ordering.Decision α ε)) : Bool :=
  (c.script.filterMap (scriptShape c b)) == (word.filterMap decisionShape)

/-- The `Prop` face of `profileCheck`. -/
def SourceProfileCompatible {α ε : Type} (c : Certificate) (b : Binding)
    (word : List (Semantics.Ordering.Decision α ε)) : Prop :=
  profileCheck c b word = true

/-- The two faces agree by definition. -/
theorem sourceProfileCompatible_iff {α ε : Type} (certificate : Certificate) (binding : Binding)
    (word : List (Semantics.Ordering.Decision α ε)) :
    SourceProfileCompatible certificate binding word ↔
      profileCheck certificate binding word = true := Iff.rfl

/-! ## §K The pinned certificate, reference and prefix -/

/-- The pinned certificate of the selected case. Symbols: `W0 = 0`, `W1 = 1`,
`W2 = 2` are the three writer results in chunk order, `D0 = 3`, `D1 = 4`,
`D2 = 5` the observers' derived results, `F = 6` the flush result and `A = 7`
the assertion result. Handlers are the fresh source names `10` to `14`. -/
def wptCertificate : Certificate :=
  Certificate.mk wptScript
    [ Attachment.mk .nestedObserverAttachment 0 10 3 (some 0)
    , Attachment.mk .nestedObserverAttachment 1 11 4 (some 1)
    , Attachment.mk .outerObserverAttachment 2 12 5 (some 2)
    , Attachment.mk .flushAttachment 5 13 6 none
    , Attachment.mk .assertionCall 6 14 7 none ]
    [ (3, .primitive), (4, .primitive), (5, .primitive), (6, .promise), (7, .primitive) ]
    [0, 1, 2]

/-- The pinned causal reference prefix. It ends after the outer observer's
reaction finishes and before the flush handler starts, so it covers the whole
asserted array; the flush and assertion attachments and the derived results'
settlements are the events `referenceErase` deletes. -/
def wptReference : List ReferenceEvent :=
  [ .logged (.size 2)
  , .logged (.size 1)
  , .logged (.size 0)
  , .attached 0
  , .attached 1
  , .attached 2
  , .attached 3
  , .attached 4
  , .scriptReturned
  , .logged (.sink 0)
  , .settled 0
  , .enqueued 0
  , .logged (.sink 1)
  , .settled 1
  , .enqueued 1
  , .started 0
  , .logged (.observer 0)
  , .returned 0
  , .settled 3
  , .finished 0
  , .logged (.sink 2)
  , .settled 2
  , .enqueued 2
  , .started 1
  , .logged (.observer 1)
  , .returned 1
  , .settled 4
  , .finished 1
  , .started 2
  , .logged (.observer 2)
  , .returned 2
  , .settled 5
  , .enqueued 3
  , .finished 2 ]

/-- The selected-log prefix of the asserted array of §3.1, transcribed as data.
It is a **report**, not a check: no checker above takes it as an argument, and
`wptReference_selected` only says what the pinned reference produces. The
numeric chunk values of the array are the host replay P8 owes; what is compared
here is the role-and-identity sequence. -/
def wptSelectedPrefix : List SelectedLog :=
  [ .size 2, .size 1, .size 0
  , .sink 0, .sink 1, .observer 0
  , .sink 2, .observer 1, .observer 2 ]

/-- Non-vacuity receipt 1: the pinned certificate passes its own checker. -/
theorem wptCertificate_checked : sourceCheck wptCertificate = true := by decide

/-- Non-vacuity receipt 2: the pinned reference is causal for it. -/
theorem wptReference_causal : causalCheck wptCertificate wptReference = true := by decide

/-- Non-vacuity receipt 3: the erased reference's selected logs are the prefix
of §3.1 of the contract. -/
theorem wptReference_selected :
    referenceSelectedLogs (referenceErase wptCertificate wptReference) = wptSelectedPrefix := by
  decide

/-! ## §L The three certificate mutants -/

/-- A selected handler on `D0`: a sixth attachment observes the first observer's
derived result and is selected. `selectedOnWriterResults` rejects it, and it is
the certificate for which the first conjunct of
`erasure_preserves_selected_order` would fail. -/
def mutantSelectedD0 : Certificate :=
  Certificate.mk
    (wptScript.take 13 ++ [.attach 5, .scriptReturn])
    (wptCertificate.attachments ++ [Attachment.mk .nestedObserverAttachment 3 15 8 none])
    (wptCertificate.returns ++ [(8, .primitive)])
    [0, 1, 2, 5]

/-- Aliased derived results: two attachments claim one derived result.
`freshDerivedOk` rejects it. -/
def mutantAliasedResults : Certificate :=
  Certificate.mk wptScript
    [ Attachment.mk .nestedObserverAttachment 0 10 3 (some 0)
    , Attachment.mk .nestedObserverAttachment 1 11 3 (some 1)
    , Attachment.mk .outerObserverAttachment 2 12 5 (some 2)
    , Attachment.mk .flushAttachment 5 13 6 none
    , Attachment.mk .assertionCall 6 14 7 none ]
    [ (3, .primitive), (3, .primitive), (5, .primitive), (6, .promise), (7, .primitive) ]
    [0, 1, 2]

/-- A flush that depends on `W0` instead of `D2`. `flushReceiverOk` rejects
it. -/
def mutantFlushOnW0 : Certificate :=
  Certificate.mk wptScript
    [ Attachment.mk .nestedObserverAttachment 0 10 3 (some 0)
    , Attachment.mk .nestedObserverAttachment 1 11 4 (some 1)
    , Attachment.mk .outerObserverAttachment 2 12 5 (some 2)
    , Attachment.mk .flushAttachment 0 13 6 none
    , Attachment.mk .assertionCall 6 14 7 none ]
    [ (3, .primitive), (4, .primitive), (5, .primitive), (6, .promise), (7, .primitive) ]
    [0, 1, 2]

/-- Rejection receipt: without it `sourceCheck = fun _ => true` would satisfy
every receipt above. Decided without consulting the expected WPT output array,
which `sourceCheck`'s signature enforces. -/
theorem sourceCheck_rejects_selectedD0 : sourceCheck mutantSelectedD0 = false := by decide

/-- Rejection receipt, as above. -/
theorem sourceCheck_rejects_aliasedResults : sourceCheck mutantAliasedResults = false := by
  decide

/-- Rejection receipt, as above. -/
theorem sourceCheck_rejects_flushOnW0 : sourceCheck mutantFlushOnW0 = false := by decide

/-! ## §M The target-side consequence -/

/-- Binding a reference trace renames its logs and nothing else about them. -/
private theorem referenceSelectedLogs_bindReference (b : Binding)
    (reference : List ReferenceEvent) :
    referenceSelectedLogs (bindReference b reference) =
      bindLogs b (referenceSelectedLogs reference) := by
  have hfun : (logOf ∘ bindEvent b) = (fun e => (logOf e).map (bindLog b)) := by
    funext e
    cases e <;> rfl
  simp only [referenceSelectedLogs, bindReference, bindLogs, List.filterMap_map,
    List.map_filterMap, hfun]

/--
The half of the old `run_erases_to_reference` that is about the erasure and is
provable from it: given the witness, the configuration's selected logs are the
reference's, bound.

It is short, and it is honest about being short — the WPT content lives in
`SourceChecked`, `CausalPrefix` and `erasure_preserves_selected_order`, and in
the existence half P8 owes. Stating it here is what makes `ErasesPrefix` worth
having: an `ErasesPrefix` witness for a source-checked certificate and a causal
reference is exactly the thing from which the ordering conclusion follows.
-/
theorem erases_prefix_selected_order {α ε : Type} (certificate : Certificate)
    (binding : Binding) (reference : List ReferenceEvent)
    (target : List (Semantics.Ordering.Event α ε))
    (hs : SourceChecked certificate) (hc : CausalPrefix certificate reference)
    (he : ErasesPrefix certificate binding reference target) :
    selectedLogs target = bindLogs binding (referenceSelectedLogs reference) := by
  rw [selectedLogs, ← he, referenceSelectedLogs_bindReference,
    (erasure_preserves_selected_order certificate reference hs hc).2]

end Whatwg.Streams.Semantics.Ordering.Source
