import Whatwg.Ecma262

/-!
Breaker-owned Q3 exact-signature battery for `Whatwg.Ecma262.Promise`.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, opened in `docs/PROMISE-DAG.md`.

Every ascription cites an extraction row (`E-…`) of
`docs/PROMISE-EXTRACTION-INVENTORY.md` with its reuse mode, or a gap id
(`G-…`) with the ES2026 census row it realizes. Byte spans are 0-based, ends
exclusive, into `vendor/ecma262-0248456c/spec.html`
(SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`).
Row ids are those of `generated/ecma262-census.tsv`. No row becomes covered
here: this battery ascribes declarations, not coverage.

`Whatwg/Ecma262/Promise.lean` imports `Whatwg.Ecma262.Jobs` and
`Whatwg.Infra`, and nothing else (DB-11). The reason parameter stays free
(decision 2): `Whatwg.WebIdl.Exceptions` is the instantiation Streams uses.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## Part A — the moved carriers

`E-01` (move). `Whatwg.Streams.Readable.PromiseState α ε` becomes
`abbrev … := Whatwg.Ecma262.Promise.State α (Whatwg.Streams.Boundary.Exception ε)`.
Two parameters per R-P13: `E-22` (`Readable.State.readPromises`) already needs
a non-unit value. The constructor names and field names are the Streams ones,
so dot-notation and every `.pending` / `.fulfilled v` / `.rejected e` in
`Whatwg/Streams/**` resolves unchanged.
Anchors: `slot.PromiseState`, 2744957..2745252, digest
`b752fb3cead6b7d3063935ef7a5867b1af9f1f298b688dbe9d015540012f33fb`;
`slot.PromiseResult`, 2745263..2745619, digest
`c0c3b1b3c19902cdec5971211ec6f5cce01d5a5696f5728c480c61013cbb9a2f`. -/

#check (@Whatwg.Ecma262.Promise.State :
  Type → Type → Type)

#check (@Whatwg.Ecma262.Promise.State.pending :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.State value reason)

#check (@Whatwg.Ecma262.Promise.State.fulfilled :
  ∀ {value reason : Type}, value → Whatwg.Ecma262.Promise.State value reason)

#check (@Whatwg.Ecma262.Promise.State.rejected :
  ∀ {value reason : Type}, reason → Whatwg.Ecma262.Promise.State value reason)

/-! `E-01` risk: `deriving DecidableEq, Repr` must survive as instances found
through the reducible Streams abbrev, or `decide` and the `simp` normal forms
in `Whatwg/Streams/Writable/Laws.lean` change. -/
#check (inferInstance :
  DecidableEq (Whatwg.Ecma262.Promise.State Nat Nat))

#check (inferInstance :
  Repr (Whatwg.Ecma262.Promise.State Nat Nat))

/-! `E-02` (move). `Whatwg.Streams.Readable.PullAnswer ε` becomes
`abbrev … := Whatwg.Ecma262.Promise.Outcome (Whatwg.Streams.Boundary.Exception ε)`.
One parameter, not two: `Readable.PullAnswer.fulfilled` takes no argument, and
a two-parameter `Outcome value reason` would break every `.fulfilled` use site
in `Whatwg/Streams/**`, which R-P12 forbids. The value-carrying settled outcome
is `Except reason value` and is deliberately not minted a second time.
Anchors: `op.fulfillpromise`, 2695419..2696230, digest
`f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e`;
`op.rejectpromise`, 2699323..2700252, digest
`1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056`. -/

#check (@Whatwg.Ecma262.Promise.Outcome :
  Type → Type)

#check (@Whatwg.Ecma262.Promise.Outcome.fulfilled :
  ∀ {reason : Type}, Whatwg.Ecma262.Promise.Outcome reason)

#check (@Whatwg.Ecma262.Promise.Outcome.rejected :
  ∀ {reason : Type}, reason → Whatwg.Ecma262.Promise.Outcome reason)

#check (inferInstance :
  DecidableEq (Whatwg.Ecma262.Promise.Outcome Nat))

#check (inferInstance :
  Repr (Whatwg.Ecma262.Promise.Outcome Nat))

/-! `E-03` (move). `Whatwg.Streams.Readable.PullReturn ε` becomes
`abbrev … := Whatwg.Ecma262.Promise.Returned (Whatwg.Streams.Boundary.Exception ε)`:
the `[[PromiseState]]` of a returned promise observed at callback-return time,
before any reaction runs. Decision 6 keeps all three carriers distinct; their
isomorphisms are bridging lemmas, not identifications. -/

#check (@Whatwg.Ecma262.Promise.Returned :
  Type → Type)

#check (@Whatwg.Ecma262.Promise.Returned.pending :
  ∀ {reason : Type}, Whatwg.Ecma262.Promise.Returned reason)

#check (@Whatwg.Ecma262.Promise.Returned.settled :
  ∀ {reason : Type}, Whatwg.Ecma262.Promise.Outcome reason →
    Whatwg.Ecma262.Promise.Returned reason)

#check (inferInstance :
  DecidableEq (Whatwg.Ecma262.Promise.Returned Nat))

#check (inferInstance :
  Repr (Whatwg.Ecma262.Promise.Returned Nat))

/-! ## Part A — promise identity

`E-14`, `E-23` (generalize) and decision 3: identities stay `Nat` with a
monotone cursor, because P6's `Transform.initial` and P7's run witnesses fix
concrete values. `Ref` is the owner-qualified pair above them (P8a rename
class "rename only"); `PromiseRef.local` is renamed `Ref.cell` because `local`
is a Lean 4 keyword and cannot be a field name. Streams keeps bare `Nat` under
a single-owner view until P8. -/

#check (@Whatwg.Ecma262.Promise.Ref :
  Type)

#check (@Whatwg.Ecma262.Promise.Ref.mk :
  Nat → Nat → Whatwg.Ecma262.Promise.Ref)

#check (@Whatwg.Ecma262.Promise.Ref.owner :
  Whatwg.Ecma262.Promise.Ref → Nat)

#check (@Whatwg.Ecma262.Promise.Ref.cell :
  Whatwg.Ecma262.Promise.Ref → Nat)

#check (inferInstance :
  DecidableEq Whatwg.Ecma262.Promise.Ref)

/-! ## Part A — the general promise table

`E-13`, `E-14`, `E-15`, `E-18`, `E-19`, `E-20`, `E-21`, `E-22`, `E-23`
(generalize). `Writable.State.promises`/`nextPromise`/`handled` and
`Readable.State.readPromises`/`nextRead` become two instances of one
append-only table over `Nat` ids at two different value parameters.
Decision 9 puts `handled` in the cell rather than in a separate identity list.
Anchors: `table-internal-slots-of-promise-instances`, the clause row
`clause.properties-of-promise-instances`, 2744135..2746691;
`slot.PromiseIsHandled`, 2746322..2746637, digest
`c5e0730a73986eb475cb399584433d21e4aadecc069e3b2d61517937d39ed652`. -/

#check (@Whatwg.Ecma262.Promise.Cell :
  Type → Type → Type)

#check (@Whatwg.Ecma262.Promise.Cell.mk :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.State value reason → Bool →
    Whatwg.Ecma262.Promise.Cell value reason)

#check (@Whatwg.Ecma262.Promise.Cell.state :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Cell value reason →
    Whatwg.Ecma262.Promise.State value reason)

#check (@Whatwg.Ecma262.Promise.Cell.handled :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Cell value reason → Bool)

#check (@Whatwg.Ecma262.Promise.Table :
  Type → Type → Type)

#check (@Whatwg.Ecma262.Promise.Table.mk :
  ∀ {value reason : Type}, List (Nat × Whatwg.Ecma262.Promise.Cell value reason) → Nat →
    Whatwg.Ecma262.Promise.Table value reason)

#check (@Whatwg.Ecma262.Promise.Table.entries :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason →
    List (Nat × Whatwg.Ecma262.Promise.Cell value reason))

#check (@Whatwg.Ecma262.Promise.Table.next :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat)

#check (inferInstance :
  DecidableEq (Whatwg.Ecma262.Promise.Table Unit Nat))

#check (@Whatwg.Ecma262.Promise.Table.empty :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason)

/-! `E-18` (generalize): the target of `Writable.lookupPromise`, which is named
in all four `attribute [local simp]` sets. -/
#check (@Whatwg.Ecma262.Promise.Table.getCell :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Option (Whatwg.Ecma262.Promise.Cell value reason))

#check (@Whatwg.Ecma262.Promise.Table.get :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Option (Whatwg.Ecma262.Promise.State value reason))

#check (@Whatwg.Ecma262.Promise.Table.isPending :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat → Bool)

/-! `E-19` (generalize): the target of `Writable.freshPromise`. The Streams
instance additionally appends a `.settled` trace event in two of its three
branches; the trace stays in Streams, so the general function allocates only. -/
#check (@Whatwg.Ecma262.Promise.Table.fresh :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.State value reason →
    Whatwg.Ecma262.Promise.Table value reason × Nat)

/-! `E-20` (generalize) and decision 7: the total guarded function. -/
#check (@Whatwg.Ecma262.Promise.Table.settle :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Except reason value → Whatwg.Ecma262.Promise.Table value reason)

/-! `E-21` (generalize): the target of `Writable.markHandled`. R-P4 keeps
`op.mark-a-promise-as-handled` an uncovered denominator row because the pinned
Streams *source* invokes it zero times; the Streams *model* already implements
it at two call sites, so this packet must not declare it absent. -/
#check (@Whatwg.Ecma262.Promise.Table.markHandled :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Whatwg.Ecma262.Promise.Table value reason)

/-! ## Part A/B — reactions and registration

`E-29`..`E-33`, `E-37`, `E-38` (generalize) supply the extraction; `G-01`
supplies the gap. Decision 8 splits the one Streams subscription list into the
two ES2026 lists, with `Reactions.registered` as the one-list view Streams
instantiates. `Reaction.kind` is the `[[Type]]` field and is new content under
`G-01`, not a rename: Streams has no such tag.
Anchors: `record.promisereaction-records`, 2690445..2692671, digest
`d66fc8081d7a889ffbdd77b8a4828c5ad87095a72fa04b257f808dbea8816743`;
`field.promisereaction-records.Capability`, 2691475..2691802;
`field.promisereaction-records.Type`, 2691815..2692138;
`field.promisereaction-records.Handler`, 2692151..2692611;
`slot.PromiseFulfillReactions`, 2745630..2745966;
`slot.PromiseRejectReactions`, 2745977..2746311. -/

#check (@Whatwg.Ecma262.Promise.ReactionType :
  Type)

#check (@Whatwg.Ecma262.Promise.ReactionType.fulfill :
  Whatwg.Ecma262.Promise.ReactionType)

#check (@Whatwg.Ecma262.Promise.ReactionType.reject :
  Whatwg.Ecma262.Promise.ReactionType)

#check (inferInstance :
  DecidableEq Whatwg.Ecma262.Promise.ReactionType)

/-! P8a rename class "rename only": `Semantics.Ordering.ObserverPhase` becomes
`Whatwg.Ecma262.Promise.ReactionPhase` with its four constructors unchanged.
`E-36` (keep) fixes that `Writable.OperationPhase` is *not* unified with it in
this packet: its fourteen receipts guard `acceptAnswer` and `attachSink`. -/
#check (@Whatwg.Ecma262.Promise.ReactionPhase :
  Type)

#check (@Whatwg.Ecma262.Promise.ReactionPhase.waiting :
  Whatwg.Ecma262.Promise.ReactionPhase)

#check (@Whatwg.Ecma262.Promise.ReactionPhase.queued :
  Nat → Whatwg.Ecma262.Promise.ReactionPhase)

#check (@Whatwg.Ecma262.Promise.ReactionPhase.running :
  Nat → Whatwg.Ecma262.Promise.ReactionPhase)

#check (@Whatwg.Ecma262.Promise.ReactionPhase.done :
  Whatwg.Ecma262.Promise.ReactionPhase)

#check (inferInstance :
  DecidableEq Whatwg.Ecma262.Promise.ReactionPhase)

/-! `E-29` (generalize) and P8a `Registration` (rename only). `handler` is
`Option body` because `field.promisereaction-records.Handler` admits an empty
handler, which is what Web IDL's one-sided "upon fulfillment" and "upon
rejection" register. `E-29` risk: `deriving Repr` only — the general record
must not gain `DecidableEq`, or `Transform.State` stops being `Repr`-only in
the same way. -/
#check (@Whatwg.Ecma262.Promise.Reaction :
  Type → Type)

/-! **Amended by the Q3b fidelity addendum, 2026-09-07**
(`test/contracts/promise-first-packet-q3b.contract.md`, finding F4,
WS-PROM-CE-026). Superseded ascription:

```lean
#check (@Whatwg.Ecma262.Promise.Reaction.mk :
  ∀ {body : Type}, Nat → Nat → Whatwg.Ecma262.Promise.ReactionType → Option body →
    Whatwg.Ecma262.Promise.ReactionPhase → Whatwg.Ecma262.Promise.Reaction body)
```

Reason: `record.promisereaction-records` (2690445..2692671) lists
`[[Capability]]` first — `field.promisereaction-records.Capability`,
2691475..2691802, digest
`67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77` — and
`op.newpromisereactionjob` (2702885..2705591) reads it to resolve or reject the
derived promise. Without the field `op.performpromisethen`'s capability
argument is stored nowhere and `G-03`'s resolving functions settle nothing. The
field sits between `handler` and `phase`, so the record still reads in the
order the two source tables give. `E-50` (generalize) constrains the repair:
`Reaction` must stay `Repr`-only. -/
#check (@Whatwg.Ecma262.Promise.Reaction.mk :
  ∀ {body : Type}, Nat → Nat → Whatwg.Ecma262.Promise.ReactionType → Option body →
    Option Whatwg.Ecma262.Promise.Capability →
    Whatwg.Ecma262.Promise.ReactionPhase → Whatwg.Ecma262.Promise.Reaction body)

#check (@Whatwg.Ecma262.Promise.Reaction.id :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Nat)

/-! `E-30` (generalize): the target of `Transform.subscriptionPromise`, the
identity captured at registration, independent of later slot replacement. -/
#check (@Whatwg.Ecma262.Promise.Reaction.promise :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Nat)

#check (@Whatwg.Ecma262.Promise.Reaction.kind :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body →
    Whatwg.Ecma262.Promise.ReactionType)

#check (@Whatwg.Ecma262.Promise.Reaction.handler :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Option body)

#check (@Whatwg.Ecma262.Promise.Reaction.phase :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body →
    Whatwg.Ecma262.Promise.ReactionPhase)

#check (inferInstance :
  Repr (Whatwg.Ecma262.Promise.Reaction Nat))

/-! `G-01`: the two reaction lists Streams does not have. -/
#check (@Whatwg.Ecma262.Promise.Reactions :
  Type → Type)

#check (@Whatwg.Ecma262.Promise.Reactions.mk :
  ∀ {body : Type}, List (Whatwg.Ecma262.Promise.Reaction body) →
    List (Whatwg.Ecma262.Promise.Reaction body) → Nat →
    Whatwg.Ecma262.Promise.Reactions body)

#check (@Whatwg.Ecma262.Promise.Reactions.fulfill :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body →
    List (Whatwg.Ecma262.Promise.Reaction body))

#check (@Whatwg.Ecma262.Promise.Reactions.reject :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body →
    List (Whatwg.Ecma262.Promise.Reaction body))

#check (@Whatwg.Ecma262.Promise.Reactions.next :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat)

#check (@Whatwg.Ecma262.Promise.Reactions.empty :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body)

/-! Keyed by list *and* id: `Reactions.add` gives the two paired entries one
shared id, so an id alone does not name a reaction. -/
#check (@Whatwg.Ecma262.Promise.Reactions.get :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Promise.ReactionType → Nat →
    Option (Whatwg.Ecma262.Promise.Reaction body))

/-! **Amended by the Q3b fidelity addendum, 2026-09-07** (finding F4,
WS-PROM-CE-026). Superseded ascription:

```lean
#check (@Whatwg.Ecma262.Promise.Reactions.add :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat → Option body → Option body →
    Whatwg.Ecma262.Promise.Reactions body × Nat)
```

Reason: `op.performpromisethen` steps 7 and 8 give **both** records the same
`_resultCapability_`, so the registering operation must take it. Streams
supplies `none`: a transform subscription has no result capability, which is
`G-11`'s remainder and is recorded as such rather than smoothed. -/
#check (@Whatwg.Ecma262.Promise.Reactions.add :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat → Option body → Option body →
    Option Whatwg.Ecma262.Promise.Capability →
    Whatwg.Ecma262.Promise.Reactions body × Nat)

#check (@Whatwg.Ecma262.Promise.Reactions.setPhase :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Promise.ReactionType → Nat →
    Whatwg.Ecma262.Promise.ReactionPhase → Whatwg.Ecma262.Promise.Reactions body)

#check (@Whatwg.Ecma262.Promise.Reactions.waitingOn :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat →
    Whatwg.Ecma262.Promise.ReactionType → List (Whatwg.Ecma262.Promise.Reaction body))

/-! Decision 8's one-list view: a registration made by `WebIdl.Promise.react`
contributes one entry to each list under one id, so the fulfil list alone is
the registration order `Transform.State.subscriptions` records. -/
#check (@Whatwg.Ecma262.Promise.Reactions.registered :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body →
    List (Whatwg.Ecma262.Promise.Reaction body))

/-! `E-33` (generalize) and its missing order law. `Transform.settle` folds
`notify` over the filtered subscription list and has only `settle_pending` and
`settle_other`; the once-only, registration-order law is new content.
Anchor: `op.triggerpromisereactions`, 2700260..2701212, digest
`ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839`. -/

#check (@Whatwg.Ecma262.Promise.triggerReactions :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat →
    Whatwg.Ecma262.Promise.ReactionType → Except reason value →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))

#check (@Whatwg.Ecma262.Promise.Table.settleAndTrigger :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → Except reason value →
    Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))

#check (@Whatwg.Ecma262.Promise.fulfillPromise :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → value →
    Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))

#check (@Whatwg.Ecma262.Promise.rejectPromise :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → reason →
    Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))

/-! ## Part B — the capability record and the resolving functions

`G-03`, wholly absent from Streams. `[[Resolve]]` and `[[Reject]]` are
first-order function identities, never Lean functions: the representation rule
in `AGENTS.md` forbids storing a body. `G-05` (thenable adoption) stays out of
this packet, so `callResolve` resolves with a plain value only.
Anchors: `record.promisecapability-records`, 2687751..2690437, digest
`08c37430874eb8f162eb3e84825cfecf3aae49700ec1a28e9728864e79fe83ab`;
`field.promisecapability-records.Promise`, 2688749..2688997;
`field.promisecapability-records.Resolve`, 2689010..2689283;
`field.promisecapability-records.Reject`, 2689296..2689567;
`op.newpromisecapability`, 2696238..2698770, digest
`9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9`;
`op.createresolvingfunctions`, 2692679..2695411, digest
`8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944`. -/

#check (@Whatwg.Ecma262.Promise.Capability :
  Type)

#check (@Whatwg.Ecma262.Promise.Capability.mk :
  Nat → Nat → Nat → Whatwg.Ecma262.Promise.Capability)

#check (@Whatwg.Ecma262.Promise.Capability.promise :
  Whatwg.Ecma262.Promise.Capability → Nat)

#check (@Whatwg.Ecma262.Promise.Capability.resolve :
  Whatwg.Ecma262.Promise.Capability → Nat)

#check (@Whatwg.Ecma262.Promise.Capability.reject :
  Whatwg.Ecma262.Promise.Capability → Nat)

#check (inferInstance :
  DecidableEq Whatwg.Ecma262.Promise.Capability)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions :
  Type)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.mk :
  Nat → Nat → Nat → Bool → Whatwg.Ecma262.Promise.ResolvingFunctions)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.promise :
  Whatwg.Ecma262.Promise.ResolvingFunctions → Nat)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.resolve :
  Whatwg.Ecma262.Promise.ResolvingFunctions → Nat)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.reject :
  Whatwg.Ecma262.Promise.ResolvingFunctions → Nat)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.alreadyResolved :
  Whatwg.Ecma262.Promise.ResolvingFunctions → Bool)

#check (inferInstance :
  DecidableEq Whatwg.Ecma262.Promise.ResolvingFunctions)

#check (@Whatwg.Ecma262.Promise.newPromiseCapability :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Capability)

#check (@Whatwg.Ecma262.Promise.createResolvingFunctions :
  Nat → Nat → Whatwg.Ecma262.Promise.ResolvingFunctions)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Table value reason → value →
    Whatwg.Ecma262.Promise.ResolvingFunctions × Whatwg.Ecma262.Promise.Table value reason)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callReject :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Table value reason → reason →
    Whatwg.Ecma262.Promise.ResolvingFunctions × Whatwg.Ecma262.Promise.Table value reason)

/-! ## Part B — `PerformPromiseThen` as a whole operation

`G-11`. Streams has steps 8 to 10 twice over (`E-31`, `E-37`), specialized and
with no result capability, so `react` returns nothing and nothing chains. This
is the operation with its capability argument and its returned promise
identity. `then`/`catch`/`finally` and the four combinators stay out.
Anchor: `op.performpromisethen`, 2740635..2743669, digest
`ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce`. -/

/-! **Amended by the Q3b fidelity addendum, 2026-09-07** (findings F1 and F2,
WS-PROM-CE-023 and WS-PROM-CE-024). Superseded ascription:

```lean
#check (@Whatwg.Ecma262.Promise.performPromiseThen :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → Option body → Option body → Option Whatwg.Ecma262.Promise.Capability →
    Option (Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option Nat))
```

Reason: steps 10 and 11 append nothing, so the PromiseReaction Record the job
captures is not reachable through `Reactions` and the operation must return it.
The fourth component is `none` on the pending branch, where step 9 appended
both records, and `some` on a settled branch, where the record was captured by
the Job Abstract Closure and by nothing else. The arguments are unchanged: the
result capability is still `Option Capability`, and the returned `Option Nat`
is still steps 13 and 14. Holding the capture is the caller's, which is the
honest reading of "captures _reaction_ and _argument_" and leaves the
identity's resolution to the P8 configuration. -/
#check (@Whatwg.Ecma262.Promise.performPromiseThen :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → Option body → Option body → Option Whatwg.Ecma262.Promise.Capability →
    Option (Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body) × Option Nat))
