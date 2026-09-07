import Whatwg.WebIdl

/-!
Breaker-owned Q3 exact-signature and law battery for `Whatwg.WebIdl.Promise`.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, opened in `docs/PROMISE-DAG.md`.

Byte spans are 0-based, ends exclusive, into
`vendor/whatwg-webidl-a652053f/index.bs`
(SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`).
Row ids are those of `generated/webidl-census.tsv`; per R-P17 the frozen
`op.dfn-perform-steps-once-promise-is-settled` and `op.waiting-for-all-promise`
spellings stand and the survey's `op.react` spelling is not adopted. Citing a
row id here anchors a declaration; it does not move a coverage state.

Masks (DB-04): a law that observes the order in which reaction jobs are queued
is **M2**; a law that observes only a value, a branch or a terminal result is
**M1**. Each block names its mask.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## The three allocating operations

`E-19` (generalize) supplies the ES2026 core: `Writable.freshPromise` already
is `NewPromiseCapability(%Promise%)` restricted to the intrinsic constructor,
followed immediately by `FulfillPromise`/`RejectPromise` when a settled outcome
is supplied. `G-03` supplies what is missing: the capability record itself,
which `Whatwg.Ecma262.Promise` now owns. These three are the Web IDL names.
Anchors: `op.a-new-promise`, 347604..347946, digest
`a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3`, 18 Streams
invocations; `op.a-promise-resolved-with`, 347948..348631, digest
`a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015`, 46;
`op.a-promise-rejected-with`, 348633..349214, digest
`3f6d84e5da374f56e56aebba956939b54dbefb219a67137a37128ecce58f20f8`, 46. -/

#check (@Whatwg.WebIdl.Promise.newPromise :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Table value reason × Nat)

#check (@Whatwg.WebIdl.Promise.resolvedWith :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → value →
    Whatwg.Ecma262.Promise.Table value reason × Nat)

#check (@Whatwg.WebIdl.Promise.rejectedWith :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → reason →
    Whatwg.Ecma262.Promise.Table value reason × Nat)

#check (@Whatwg.WebIdl.Promise.newPromise_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason),
    Whatwg.WebIdl.Promise.newPromise t =
      Whatwg.Ecma262.Promise.Table.fresh t Whatwg.Ecma262.Promise.State.pending)

#check (@Whatwg.WebIdl.Promise.resolvedWith_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (v : value),
    Whatwg.WebIdl.Promise.resolvedWith t v =
      Whatwg.Ecma262.Promise.Table.fresh t (Whatwg.Ecma262.Promise.State.fulfilled v))

#check (@Whatwg.WebIdl.Promise.rejectedWith_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason),
    Whatwg.WebIdl.Promise.rejectedWith t r =
      Whatwg.Ecma262.Promise.Table.fresh t (Whatwg.Ecma262.Promise.State.rejected r))

/-! ## The two settling operations and the handled bit

`E-20`, `E-21` (generalize). Anchors: `op.resolve`, 349216..349783, digest
`071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3`, 35 Streams
invocations; `op.reject`, 349785..350073, digest
`c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea`, 23;
`op.mark-a-promise-as-handled`, 356060..356713, digest
`644263e9155cf45d31167e53346f9d0e2431aedde301b440dbc92d9021b618bc`, 0 Streams
source invocations under R-P4 but two call sites in the Streams *model*
(`Writable/Backpressure.lean` and `Writable/DefaultController.lean`), so this
packet must not present it as absent from Streams. Its census row stays
`absent`; this declaration is not a coverage witness. -/

#check (@Whatwg.WebIdl.Promise.resolve :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat → value →
    Whatwg.Ecma262.Promise.Table value reason)

#check (@Whatwg.WebIdl.Promise.reject :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat → reason →
    Whatwg.Ecma262.Promise.Table value reason)

#check (@Whatwg.WebIdl.Promise.markAsHandled :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Whatwg.Ecma262.Promise.Table value reason)

#check (@Whatwg.WebIdl.Promise.resolve_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat)
    (v : value),
    Whatwg.WebIdl.Promise.resolve t id v =
      Whatwg.Ecma262.Promise.Table.settle t id (Except.ok v))

#check (@Whatwg.WebIdl.Promise.reject_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat)
    (r : reason),
    Whatwg.WebIdl.Promise.reject t id r =
      Whatwg.Ecma262.Promise.Table.settle t id (Except.error r))

#check (@Whatwg.WebIdl.Promise.markAsHandled_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.WebIdl.Promise.markAsHandled t id = Whatwg.Ecma262.Promise.Table.markHandled t id)

/-! ## `react` and the two one-sided wrappers

`E-31`, `E-37` (generalize): `Transform.subscribe` and `Writable.attachSink`
are two independently written instances of the same `PerformPromiseThen`
steps 8 to 10 case split, and `E-31`'s four receipts
(`subscribe_pending/_fulfilled/_rejected/_missing`) are exactly that split.
The general operation keeps `E-31`'s `Option` result: a missing cell has no
transition. It returns no derived promise; that remainder is `G-11` and is
`Whatwg.Ecma262.Promise.performPromiseThen`.
Anchors: `op.dfn-perform-steps-once-promise-is-settled`, 350075..352408, digest
`dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383`, 8 Streams
invocations; `op.upon-fulfillment`, 352410..352816, digest
`81ccd0a141715f38ae30f05c97a994c4ea3fef748c6301da8f3b8e4c6c785b9d`, 9;
`op.upon-rejection`, 352818..353237, digest
`f1e47b988febfd3652dac64ddb390db465d96a07f5b2d939cd8c62413221e7e9`, 11. -/

/-! **The three ascriptions below are amended by the Q3b fidelity addendum,
2026-09-07** (`test/contracts/promise-first-packet-q3b.contract.md`, findings
F1 and F2, WS-PROM-CE-023 and WS-PROM-CE-024). The superseded ascriptions are
the same three with the result
`Option (Reactions body × Jobs.Queue (Jobs.ReactionJob (Except reason value)))`.

Reason: `op.dfn-perform-steps-once-promise-is-settled` step 7 performs
`PerformPromiseThen`, so `react` inherits step 12 — set `[[PromiseIsHandled]]`
on every branch — and steps 10 and 11 — the settled branches append to no list
and the record the job captures is held by the caller. Neither is expressible
without the table and the captured record in the result. The **arguments** are
unchanged: step 6's `newCapability` and step 8's `Return |newCapability|` are
`G-11`'s remainder and stay out, as the base packet already records, so `react`
still takes no capability.

`uponFulfillment_eq` and `uponRejection_eq` below are **not** amended: their
statements are byte-identical and elaborate unchanged at the new result type.

The `none` those two wrappers pass on the other side is a `G-11` modelling
restriction and is **not** what the pinned text does: steps 1 to 4 of
`op.dfn-perform-steps-once-promise-is-settled` build both `onFulfilled` and
`onRejected` unconditionally, so Web IDL `react` never registers an empty
handler. §4.6's citation of this operation as the justification for
`Reaction.handler : Option body` is corrected by the addendum: the `~empty~`
handler comes from `op.performpromisethen` steps 3 and 5, the `IsCallable`
test (WS-PROM-CE-036). -/

#check (@Whatwg.WebIdl.Promise.react :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → Option body → Option body →
    Option (Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)))

#check (@Whatwg.WebIdl.Promise.uponFulfillment :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → body →
    Option (Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)))

#check (@Whatwg.WebIdl.Promise.uponRejection :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.Reactions body →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) →
    Nat → body →
    Option (Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)))

/-! Mask M1. The generalization of `Transform.subscribe_pending`.

**Amended by the Q3b fidelity addendum, 2026-09-07** (finding F1,
WS-PROM-CE-023): the superseded ascription's right-hand side was
`some ((Reactions.add rs promise onFulfilled onRejected).1, q)`. `react`
performs `PerformPromiseThen`, whose step 12 marks the promise handled on every
branch, and `add` gains the capability argument of finding F4, which `react`
supplies as `none` (step 6's `newCapability` is `G-11`'s remainder). -/
#check (@Whatwg.WebIdl.Promise.react_pending :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body),
    Whatwg.Ecma262.Promise.Table.get t promise = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.WebIdl.Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected none).1,
          q, none))

/-! Mask M2: the statement observes the reaction job entering the queue. The
generalization of `Transform.subscribe_fulfilled`.

**Amended by the Q3b fidelity addendum, 2026-09-07** (findings F1 and F2,
WS-PROM-CE-023 and WS-PROM-CE-024): the superseded ascription's right-hand side
was `some (Reactions.setPhase (Reactions.add rs promise onFulfilled onRejected).1
ReactionType.fulfill rs.next (ReactionPhase.queued rs.next), Queue.enqueue q
(ReactionJob.mk rs.next (Except.ok v)))`. It appended to both lists on a branch
where the pinned text appends to neither, and left the reject-side entry
waiting on a promise that had already fulfilled. The enqueued job is unchanged,
so the M2 content of the law is exactly what it was. -/
#check (@Whatwg.WebIdl.Promise.react_fulfilled :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (v : value) (onFulfilled onRejected : Option body),
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.fulfilled v) →
      Whatwg.WebIdl.Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled none).1,
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.ok v)),
          some (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled none).2))

/-! Mask M2. The generalization of `Transform.subscribe_rejected`.

**Amended by the Q3b fidelity addendum, 2026-09-07**, for the same two findings
and the same reason as the fulfilled branch. -/
#check (@Whatwg.WebIdl.Promise.react_rejected :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (r : reason) (onFulfilled onRejected : Option body),
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.rejected r) →
      Whatwg.WebIdl.Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.reject onRejected none).1,
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.error r)),
          some (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.reject onRejected none).2))

/-! Mask M1. The generalization of `Transform.subscribe_missing`. `E-31` risk:
`PerformPromiseThen` is total where this is partial; the packet keeps the
Streams `Option` and records the difference rather than smoothing it. -/
#check (@Whatwg.WebIdl.Promise.react_missing :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body),
    Whatwg.Ecma262.Promise.Table.get t promise = none →
      Whatwg.WebIdl.Promise.react t rs q promise onFulfilled onRejected = none)

#check (@Whatwg.WebIdl.Promise.uponFulfillment_eq :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body),
    Whatwg.WebIdl.Promise.uponFulfillment t rs q promise steps =
      Whatwg.WebIdl.Promise.react t rs q promise (some steps) none)

#check (@Whatwg.WebIdl.Promise.uponRejection_eq :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body),
    Whatwg.WebIdl.Promise.uponRejection t rs q promise steps =
      Whatwg.WebIdl.Promise.react t rs q promise none (some steps))

/-! ## `wait for all`: the predicate `E-55`/`E-56` already are, and the
operation `G-06` still needs

Decision 11 puts both in this module in this packet rather than deferring them
without an owner. `Piping.WritesSettled` (`E-55`) and `Piping.allWrittenSettled`
(`E-56`) are the settled predicate in `Prop` and `Bool` form with no stated
agreement lemma; `allSettled_iff` is that lemma and is new content.
`waitForAll` adds what `G-06` records as missing: an ordered result list and a
first-rejection short-circuit. What it still does not add is the returned
promise and the `[=Queue a microtask=]` step: `op.waiting-for-all-promise`
(354881..356058, digest
`e8e29da9e357ce2532fe7acb9b978139f217f5dbc83db043cc2f7ffeacb605b3`) is out of
this packet, and no ordering claim about it is made here.
Anchor: `op.wait-for-all`, 353239..354879, digest
`518fae182417ff76e800ed67df039a512d35b6af29ee11251b684172e703d930`. -/

#check (@Whatwg.WebIdl.Promise.AllSettled :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → List Nat → Prop)

#check (@Whatwg.WebIdl.Promise.allSettled :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → List Nat → Bool)

#check (@Whatwg.WebIdl.Promise.WaitResult :
  Type → Type → Type)

#check (@Whatwg.WebIdl.Promise.WaitResult.pending :
  ∀ {value reason : Type}, Whatwg.WebIdl.Promise.WaitResult value reason)

#check (@Whatwg.WebIdl.Promise.WaitResult.success :
  ∀ {value reason : Type}, List value → Whatwg.WebIdl.Promise.WaitResult value reason)

#check (@Whatwg.WebIdl.Promise.WaitResult.failure :
  ∀ {value reason : Type}, reason → Whatwg.WebIdl.Promise.WaitResult value reason)

#check (@Whatwg.WebIdl.Promise.waitForAll :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → List Nat →
    Whatwg.WebIdl.Promise.WaitResult value reason)

/-! Mask M1. -/
#check (@Whatwg.WebIdl.Promise.AllSettled_iff :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat),
    Whatwg.WebIdl.Promise.AllSettled t ids ↔
      ∀ id ∈ ids, (∃ v : value, Whatwg.Ecma262.Promise.Table.get t id =
          some (Whatwg.Ecma262.Promise.State.fulfilled v)) ∨
        (∃ r : reason, Whatwg.Ecma262.Promise.Table.get t id =
          some (Whatwg.Ecma262.Promise.State.rejected r)))

/-! The `Prop`/`Bool` agreement `E-56` records as absent today. Mask M1. -/
#check (@Whatwg.WebIdl.Promise.allSettled_iff :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat),
    Whatwg.WebIdl.Promise.allSettled t ids = true ↔ Whatwg.WebIdl.Promise.AllSettled t ids)

/-! Mask M1. -/
#check (@Whatwg.WebIdl.Promise.waitForAll_pending :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat),
    ¬ Whatwg.WebIdl.Promise.AllSettled t ids →
      Whatwg.WebIdl.Promise.waitForAll t ids = Whatwg.WebIdl.Promise.WaitResult.pending)

/-! Mask **M1**, relabelled from M2 by the Q3b fidelity addendum, 2026-09-07
(finding F6's minor, WS-PROM-CE-037). The statement is unchanged and stays
frozen. Reason: §7's rule makes a theorem M2 when its **statement** observes
the order in which settlements happen or in which reaction jobs enter the
queue. This statement pairs `ids` with `values` positionally — argument order —
and observes neither settlement order nor queue order; §7's table listed it
under M2, and the rule governs the table. The genuinely M2 companion is
`waitForAllTraced_failure` in `WhatwgTest/WebIdl/PromiseFidelityContract.lean`.
Offered for coordinator ratification alongside the relabel R-P20 names
explicitly, which is the one below. -/
#check (@Whatwg.WebIdl.Promise.waitForAll_success :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat)
    (values : List value),
    ids.length = values.length →
    (∀ p ∈ ids.zip values, Whatwg.Ecma262.Promise.Table.get t p.1 =
        some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
      Whatwg.WebIdl.Promise.waitForAll t ids =
        Whatwg.WebIdl.Promise.WaitResult.success values)

/-! Mask **M1**, relabelled from M2 by the Q3b fidelity addendum, 2026-09-07
(finding F6, WS-PROM-CE-030, and ruling R-P20's "`waitForAll_failure`'s M2
label overstates it"). The statement is unchanged and stays frozen: the first
rejection in **argument** order is the one this operation reports, and argument
order is neither a settlement order nor a queue order, so §7's rule makes the
theorem M1.

What `op.wait-for-all` (353239..354879) actually says is that the rejection
handler fires on the first rejection **to settle**, with the other promises
possibly still pending. That needs a settlement order the general table cannot
express, and it is stated — under a genuine M2 — as
`Whatwg.WebIdl.Promise.waitForAllTraced_failure` and
`waitForAllTraced_failure_pending` over
`Whatwg.Ecma262.Promise.SettlementTrace`. This ascription keeps its place
because `waitForAll` keeps its signature: `E-55` and `E-56` own the predicate
half and eleven Streams call sites reach it. -/
#check (@Whatwg.WebIdl.Promise.waitForAll_failure :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (before : List Nat) (id : Nat) (after : List Nat) (r : reason),
    Whatwg.WebIdl.Promise.AllSettled t (before ++ id :: after) →
    (∀ earlier ∈ before, ∃ v : value, Whatwg.Ecma262.Promise.Table.get t earlier =
        some (Whatwg.Ecma262.Promise.State.fulfilled v)) →
    Whatwg.Ecma262.Promise.Table.get t id = some (Whatwg.Ecma262.Promise.State.rejected r) →
      Whatwg.WebIdl.Promise.waitForAll t (before ++ id :: after) =
        Whatwg.WebIdl.Promise.WaitResult.failure r)
