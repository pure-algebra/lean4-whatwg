import Whatwg.Ecma262

/-!
Breaker-owned Q3 law battery for `Whatwg.Ecma262.Promise`.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`.

Masks (DB-04). A law whose statement observes the *order* of settlements or of
queued reaction jobs is **M2**; a law that observes only a cell value, a branch
or a terminal result is **M1**. Each block names its mask. Nothing here is a
claim about a host, a stream, or a census coverage state.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ### Table equations — mask M1

`E-13`, `E-18`, `E-19`, `E-20`, `E-21` (generalize). These are the general
forms of `Writable.lookupPromise_eq`, `freshPromise_pending/_fulfilled/
_rejected`, `settle_pending`, `settle_other` and `markHandled_eq`, which stay
frozen and unchanged in `Whatwg/Streams/Writable/Laws.lean`. -/

#check (@Whatwg.Ecma262.Promise.Table.empty_eq :
  ∀ {value reason : Type},
    (Whatwg.Ecma262.Promise.Table.empty : Whatwg.Ecma262.Promise.Table value reason) =
      Whatwg.Ecma262.Promise.Table.mk [] 0)

#check (@Whatwg.Ecma262.Promise.Table.getCell_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.Ecma262.Promise.Table.getCell t id =
      (t.entries.find? (fun e => e.1 == id)).map Prod.snd)

#check (@Whatwg.Ecma262.Promise.Table.get_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.Ecma262.Promise.Table.get t id =
      (Whatwg.Ecma262.Promise.Table.getCell t id).map Whatwg.Ecma262.Promise.Cell.state)

#check (@Whatwg.Ecma262.Promise.Table.isPending_iff :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.Ecma262.Promise.Table.isPending t id = true ↔
      Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending)

/-! `E-13` risk: the table is append-only, and the three `freshPromise_*`
receipts state the append shape verbatim. -/
#check (@Whatwg.Ecma262.Promise.Table.fresh_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (outcome : Whatwg.Ecma262.Promise.State value reason),
    Whatwg.Ecma262.Promise.Table.fresh t outcome =
      (Whatwg.Ecma262.Promise.Table.mk
        (t.entries ++ [(t.next, Whatwg.Ecma262.Promise.Cell.mk outcome false)]) (t.next + 1),
        t.next))

#check (@Whatwg.Ecma262.Promise.Table.fresh_id :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (outcome : Whatwg.Ecma262.Promise.State value reason),
    (Whatwg.Ecma262.Promise.Table.fresh t outcome).2 = t.next)

#check (@Whatwg.Ecma262.Promise.Table.fresh_next :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (outcome : Whatwg.Ecma262.Promise.State value reason),
    (Whatwg.Ecma262.Promise.Table.fresh t outcome).1.next = t.next + 1)

/-! Retention: allocating never overwrites an earlier cell. This is what
`E-43` (`Writable.updateBackpressure` replaces a settled ready cell with a new
one and old references keep their outcomes) depends on. -/
#check (@Whatwg.Ecma262.Promise.Table.fresh_old :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (outcome : Whatwg.Ecma262.Promise.State value reason) (id : Nat),
    id ≠ t.next →
      Whatwg.Ecma262.Promise.Table.getCell (Whatwg.Ecma262.Promise.Table.fresh t outcome).1 id =
        Whatwg.Ecma262.Promise.Table.getCell t id)

#check (@Whatwg.Ecma262.Promise.Table.fresh_get :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (outcome : Whatwg.Ecma262.Promise.State value reason),
    Whatwg.Ecma262.Promise.Table.getCell t t.next = none →
      Whatwg.Ecma262.Promise.Table.get (Whatwg.Ecma262.Promise.Table.fresh t outcome).1 t.next =
        some outcome)

/-! ### Settling: the guard, and the assertion as a side condition — mask M1

Decision 7. ES2026 `FulfillPromise` step 1 *asserts* that the promise is
pending; `Writable.settle` makes a non-pending settle the identity and
`settle_other` is a frozen receipt for exactly that. The general operation is
the total guarded function, and the specification's assertion is recovered as
`settle_assert`, a separate lemma under the pending hypothesis. -/

#check (@Whatwg.Ecma262.Promise.Table.settle_pending :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat)
    (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.settle t id result =
        Whatwg.Ecma262.Promise.Table.mk
          (t.entries.map (fun e =>
            if e.1 == id then
              (e.1, Whatwg.Ecma262.Promise.Cell.mk
                (match result with
                  | .ok v => Whatwg.Ecma262.Promise.State.fulfilled v
                  | .error r => Whatwg.Ecma262.Promise.State.rejected r) e.2.handled)
            else e))
          t.next)

#check (@Whatwg.Ecma262.Promise.Table.settle_other :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat)
    (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id ≠ some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.settle t id result = t)

#check (@Whatwg.Ecma262.Promise.Table.settle_assert :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat)
    (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.get (Whatwg.Ecma262.Promise.Table.settle t id result) id =
        some (match result with
          | .ok v => Whatwg.Ecma262.Promise.State.fulfilled v
          | .error r => Whatwg.Ecma262.Promise.State.rejected r))

#check (@Whatwg.Ecma262.Promise.Table.settle_handled :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat)
    (result : Except reason value),
    (Whatwg.Ecma262.Promise.Table.getCell (Whatwg.Ecma262.Promise.Table.settle t id result)
        id).map Whatwg.Ecma262.Promise.Cell.handled =
      (Whatwg.Ecma262.Promise.Table.getCell t id).map Whatwg.Ecma262.Promise.Cell.handled)

/-! ### The handled bit — mask M1

`E-15`, `E-21` and decision 9. `G-02` records that nothing reads the bit yet
and that `HostPromiseRejectionTracker` (`hook.host-promise-rejection-tracker`,
2701220..2702791) is out of this packet, so the only laws are placement and
idempotence. `Writable.markHandled`'s idempotence is stated today only through
`markHandled_eq`; here it is a law. -/

#check (@Whatwg.Ecma262.Promise.Table.markHandled_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.Ecma262.Promise.Table.markHandled t id =
      Whatwg.Ecma262.Promise.Table.mk
        (t.entries.map (fun e =>
          if e.1 == id then (e.1, Whatwg.Ecma262.Promise.Cell.mk e.2.state true) else e))
        t.next)

#check (@Whatwg.Ecma262.Promise.Table.markHandled_idem :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.Ecma262.Promise.Table.markHandled (Whatwg.Ecma262.Promise.Table.markHandled t id) id =
      Whatwg.Ecma262.Promise.Table.markHandled t id)

#check (@Whatwg.Ecma262.Promise.Table.markHandled_state :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    Whatwg.Ecma262.Promise.Table.get (Whatwg.Ecma262.Promise.Table.markHandled t id) id =
      Whatwg.Ecma262.Promise.Table.get t id)

/-! ### The two reaction lists — mask M1 -/

#check (@Whatwg.Ecma262.Promise.Reactions.empty_eq :
  ∀ {body : Type},
    (Whatwg.Ecma262.Promise.Reactions.empty : Whatwg.Ecma262.Promise.Reactions body) =
      Whatwg.Ecma262.Promise.Reactions.mk [] [] 0)

#check (@Whatwg.Ecma262.Promise.Reactions.get_eq :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (id : Nat),
    Whatwg.Ecma262.Promise.Reactions.get rs kind id =
      (match kind with
        | .fulfill => rs.fulfill
        | .reject => rs.reject).find? (fun r => r.id == id))

/-! **The four `add` laws below are amended by the Q3b fidelity addendum,
2026-09-07** (`test/contracts/promise-first-packet-q3b.contract.md`, finding
F4, WS-PROM-CE-026). The superseded ascriptions are the same four with
`Reactions.add`'s four arguments and `Reaction.mk`'s five, without the
capability. Reason: `op.performpromisethen` steps 7 and 8 give both records the
same `_resultCapability_`, so `add` takes it and both appended records carry
it; `add_fulfill` and `add_reject` are where that is checkable. Nothing else in
the four statements changes, and `add_paired` below is amended only in its
telescope. -/

#check (@Whatwg.Ecma262.Promise.Reactions.add_id :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
      capability).2 = rs.next)

#check (@Whatwg.Ecma262.Promise.Reactions.add_next :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
      capability).1.next = rs.next + 1)

#check (@Whatwg.Ecma262.Promise.Reactions.add_fulfill :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
        capability).1.fulfill =
      rs.fulfill ++ [Whatwg.Ecma262.Promise.Reaction.mk rs.next promise
        Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled capability
        Whatwg.Ecma262.Promise.ReactionPhase.waiting])

#check (@Whatwg.Ecma262.Promise.Reactions.add_reject :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
        capability).1.reject =
      rs.reject ++ [Whatwg.Ecma262.Promise.Reaction.mk rs.next promise
        Whatwg.Ecma262.Promise.ReactionType.reject onRejected capability
        Whatwg.Ecma262.Promise.ReactionPhase.waiting])

#check (@Whatwg.Ecma262.Promise.Reactions.setPhase_eq :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase),
    Whatwg.Ecma262.Promise.Reactions.setPhase rs kind id phase =
      (match kind with
        | .fulfill =>
            Whatwg.Ecma262.Promise.Reactions.mk
              (rs.fulfill.map (fun r => if r.id == id then { r with phase := phase } else r))
              rs.reject rs.next
        | .reject =>
            Whatwg.Ecma262.Promise.Reactions.mk rs.fulfill
              (rs.reject.map (fun r => if r.id == id then { r with phase := phase } else r))
              rs.next))

#check (@Whatwg.Ecma262.Promise.Reactions.waitingOn_eq :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType),
    Whatwg.Ecma262.Promise.Reactions.waitingOn rs promise kind =
      (match kind with
        | .fulfill => rs.fulfill
        | .reject => rs.reject).filter (fun r =>
          r.promise == promise && r.phase == Whatwg.Ecma262.Promise.ReactionPhase.waiting))

/-! Decision 8's one-list view. `Reactions.add` gives the paired entries one
id, so the fulfil list alone carries the registration order that
`Transform.State.subscriptions` records (`E-29`). -/
#check (@Whatwg.Ecma262.Promise.Reactions.registered_eq :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body),
    Whatwg.Ecma262.Promise.Reactions.registered rs = rs.fulfill)

/-! **Amended by the Q3b fidelity addendum, 2026-09-07** (finding F4): the
telescope gains `Reactions.add`'s capability argument and nothing else. -/
#check (@Whatwg.Ecma262.Promise.Reactions.add_paired :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    rs.fulfill.map Whatwg.Ecma262.Promise.Reaction.id =
        rs.reject.map Whatwg.Ecma262.Promise.Reaction.id →
      (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
          capability).1.fulfill.map Whatwg.Ecma262.Promise.Reaction.id =
        (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
          capability).1.reject.map Whatwg.Ecma262.Promise.Reaction.id)

/-! ### `TriggerPromiseReactions` — the order law `E-33` does not have

`op.triggerpromisereactions`, 2700260..2701212, whose entire content is
"enqueue a reaction job for each reaction, in list order". `Transform.settle`
folds `notify` over the filtered subscription list and states only
`settle_pending` and `settle_other`; the order and once-only laws below are new
content under `G-01`, not extraction, and the contract declares them as such. -/

/-! Mask M2: the statement observes the order in which reaction jobs enter the
queue. -/
#check (@Whatwg.Ecma262.Promise.triggerReactions_order :
  ∀ {value reason body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (argument : Except reason value)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))),
    (Whatwg.Ecma262.Promise.triggerReactions rs promise kind argument q).2.pending =
      q.pending ++ (Whatwg.Ecma262.Promise.Reactions.waitingOn rs promise kind).map
        (fun r => Whatwg.Ecma262.Jobs.ReactionJob.mk r.id argument))

/-! Mask M1: once triggered, the same promise and list have no waiting
reaction left, so no reaction job is enqueued twice. -/
#check (@Whatwg.Ecma262.Promise.triggerReactions_once :
  ∀ {value reason body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (argument : Except reason value)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))),
    Whatwg.Ecma262.Promise.Reactions.waitingOn
      (Whatwg.Ecma262.Promise.triggerReactions rs promise kind argument q).1 promise kind = [])

#check (@Whatwg.Ecma262.Promise.triggerReactions_other_promise :
  ∀ {value reason body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body)
    (promise other : Nat) (kind : Whatwg.Ecma262.Promise.ReactionType)
    (argument : Except reason value)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))),
    other ≠ promise →
      Whatwg.Ecma262.Promise.Reactions.waitingOn
          (Whatwg.Ecma262.Promise.triggerReactions rs promise kind argument q).1 other kind =
        Whatwg.Ecma262.Promise.Reactions.waitingOn rs other kind)

/-! **Annotated by the Q3b fidelity addendum, 2026-09-07** (finding F3,
WS-PROM-CE-025). The statement is unchanged and stays frozen: it is a law about
`op.triggerpromisereactions` (2700260..2701212) **alone**, whose entire content
is "enqueue a reaction job for each record in _reactions_", and which really
does not touch the other list. It must not be read as a law about
`op.fulfillpromise` or `op.rejectpromise`, whose steps 4 and 5 each set both
`[[PromiseFulfillReactions]]` and `[[PromiseRejectReactions]]` to *undefined*.
The residue this ascription froze belongs to the two callers, and the addendum
states it there: `Reactions.clear_waiting` and
`Table.settleAndTrigger_cleared` in
`WhatwgTest/Ecma262/PromiseFidelityLaws.lean`, with the amended
`Table.settleAndTrigger_pending` below giving the exact equation. Mask M1. -/
#check (@Whatwg.Ecma262.Promise.triggerReactions_other_kind :
  ∀ {value reason body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind other : Whatwg.Ecma262.Promise.ReactionType) (argument : Except reason value)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))),
    other ≠ kind →
      Whatwg.Ecma262.Promise.Reactions.waitingOn
          (Whatwg.Ecma262.Promise.triggerReactions rs promise kind argument q).1 promise other =
        Whatwg.Ecma262.Promise.Reactions.waitingOn rs promise other)

/-! ### Settle-and-trigger, `FulfillPromise` and `RejectPromise` -/

/-! Mask M2. `E-33`'s target: `op.fulfillpromise` / `op.rejectpromise`
followed by `op.triggerpromisereactions`.

**Amended by the Q3b fidelity addendum, 2026-09-07** (finding F3,
WS-PROM-CE-025). Superseded ascription:

```lean
#check (@Whatwg.Ecma262.Promise.Table.settleAndTrigger_pending :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.settleAndTrigger t rs q id result =
        (Whatwg.Ecma262.Promise.Table.settle t id result,
          Whatwg.Ecma262.Promise.triggerReactions rs id
            (match result with
              | .ok _ => Whatwg.Ecma262.Promise.ReactionType.fulfill
              | .error _ => Whatwg.Ecma262.Promise.ReactionType.reject) result q))
```

Reason: `op.fulfillpromise` steps 4 and 5 and `op.rejectpromise` steps 4 and 5
each set **both** reaction lists to *undefined*, and the base packet advanced
only the triggered one, leaving the other side's registrations waiting on a
promise that can never trigger them. `Reactions.clear` is the first-order form
of that pair of steps; the job queue component is unchanged, so the M2 content
of the law — the order in which reaction jobs enter the queue — is exactly what
it was. -/
#check (@Whatwg.Ecma262.Promise.Table.settleAndTrigger_pending :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.settleAndTrigger t rs q id result =
        (Whatwg.Ecma262.Promise.Table.settle t id result,
          Whatwg.Ecma262.Promise.Reactions.clear
            (Whatwg.Ecma262.Promise.triggerReactions rs id
              (match result with
                | .ok _ => Whatwg.Ecma262.Promise.ReactionType.fulfill
                | .error _ => Whatwg.Ecma262.Promise.ReactionType.reject) result q).1 id,
          (Whatwg.Ecma262.Promise.triggerReactions rs id
            (match result with
              | .ok _ => Whatwg.Ecma262.Promise.ReactionType.fulfill
              | .error _ => Whatwg.Ecma262.Promise.ReactionType.reject) result q).2))

/-! Mask M1. The guard of decision 7 propagates: a non-pending promise
notifies nobody. -/
#check (@Whatwg.Ecma262.Promise.Table.settleAndTrigger_other :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id ≠ some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.settleAndTrigger t rs q id result = (t, rs, q))

#check (@Whatwg.Ecma262.Promise.fulfillPromise_eq :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (id : Nat) (v : value),
    Whatwg.Ecma262.Promise.fulfillPromise t rs q id v =
      Whatwg.Ecma262.Promise.Table.settleAndTrigger t rs q id (Except.ok v))

#check (@Whatwg.Ecma262.Promise.rejectPromise_eq :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (id : Nat) (r : reason),
    Whatwg.Ecma262.Promise.rejectPromise t rs q id r =
      Whatwg.Ecma262.Promise.Table.settleAndTrigger t rs q id (Except.error r))

/-! ### `PerformPromiseThen` — mask M2 for the two settled branches

`G-11`. The three branches are exactly the case split that `E-31`'s
`subscribe_pending/_fulfilled/_rejected` and `E-37`'s `attachSink` perform
twice over in Streams, now with the result capability that neither has. Step 12
sets `[[PromiseIsHandled]]`, which is why the two settled branches mark the
promise handled. -/

#check (@Whatwg.Ecma262.Promise.performPromiseThen_missing :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    Whatwg.Ecma262.Promise.Table.get t promise = none →
      Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
        capability = none)

/-! **Amended by the Q3b fidelity addendum, 2026-09-07** (finding F1,
WS-PROM-CE-023). Superseded ascription:

```lean
#check (@Whatwg.Ecma262.Promise.performPromiseThen_pending :
  ∀ … , Whatwg.Ecma262.Promise.Table.get t promise =
          some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
          capability =
        some (t, (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1, q,
          capability.map Whatwg.Ecma262.Promise.Capability.promise))
```

Reason: `op.performpromisethen` step 12, "Set _promise_.[[PromiseIsHandled]] to
*true*", sits after the three-way branch of steps 9 to 11, not inside it. The
superseded ascription returned the table untouched and so froze the omission.
The registration half is unchanged apart from `add`'s capability argument
(finding F4), and the new fourth component is `none`, because step 9 appends
both records and captures neither. Mask M1. -/
#check (@Whatwg.Ecma262.Promise.performPromiseThen_pending :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    Whatwg.Ecma262.Promise.Table.get t promise = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
          capability =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected
            capability).1,
          q, none,
          capability.map Whatwg.Ecma262.Promise.Capability.promise))

/-! **Amended by the Q3b fidelity addendum, 2026-09-07** (finding F2,
WS-PROM-CE-024). Superseded ascription: the same statement with
`Reactions.setPhase (Reactions.add rs promise onFulfilled onRejected).1
ReactionType.fulfill rs.next (ReactionPhase.queued rs.next)` as the reactions
component and no reaction component.

Reason: `op.performpromisethen` step 10 builds `_fulfillJob_` out of the record
created at step 7 and enqueues it. It appends nothing: only step 9's pending
branch appends, and it appends one record to each list. The superseded
ascription appended to both lists and then advanced one of the two entries,
leaving the reject-side entry in the `waiting` phase on a promise that has
already fulfilled — a state the pinned text never has. `Reactions.mint` is the
unappended record and the operation returns it, because nothing else holds it.
The job queue component is unchanged, so the M2 content of the law is exactly
what it was. Mask M2. -/
#check (@Whatwg.Ecma262.Promise.performPromiseThen_fulfilled :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (v : value) (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.fulfilled v) →
      Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
          capability =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled capability).1,
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.ok v)),
          some (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled capability).2,
          capability.map Whatwg.Ecma262.Promise.Capability.promise))

/-! **Amended by the Q3b fidelity addendum, 2026-09-07** (finding F2,
WS-PROM-CE-024), for `op.performpromisethen` step 11 and the same reason as the
fulfilled branch. Step 11's third sub-step, `HostPromiseRejectionTracker`, is
`G-02` and stays out: no component here observes it. Mask M2. -/
#check (@Whatwg.Ecma262.Promise.performPromiseThen_rejected :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (r : reason) (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.rejected r) →
      Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
          capability =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.reject onRejected capability).1,
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.error r)),
          some (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.reject onRejected capability).2,
          capability.map Whatwg.Ecma262.Promise.Capability.promise))

/-! ### Capability and resolving functions — mask M1

`G-03`. `[[AlreadyResolved]]` is the one-shot marker; the thenable branch of
`CreateResolvingFunctions` is `G-05` and stays out, so `callResolve` settles
with a plain value and never looks up a `then` method. -/

#check (@Whatwg.Ecma262.Promise.newPromiseCapability_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (functionSeed : Nat),
    Whatwg.Ecma262.Promise.newPromiseCapability t functionSeed =
      ((Whatwg.Ecma262.Promise.Table.fresh t Whatwg.Ecma262.Promise.State.pending).1,
        Whatwg.Ecma262.Promise.Capability.mk
          (Whatwg.Ecma262.Promise.Table.fresh t Whatwg.Ecma262.Promise.State.pending).2
          functionSeed (functionSeed + 1)))

#check (@Whatwg.Ecma262.Promise.createResolvingFunctions_eq :
  ∀ (promise functionSeed : Nat),
    Whatwg.Ecma262.Promise.createResolvingFunctions promise functionSeed =
      Whatwg.Ecma262.Promise.ResolvingFunctions.mk promise functionSeed (functionSeed + 1) false)

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve_fresh :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value),
    f.alreadyResolved = false →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v =
        ({ f with alreadyResolved := true },
          Whatwg.Ecma262.Promise.Table.settle t f.promise (Except.ok v)))

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve_alreadyResolved :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value),
    f.alreadyResolved = true →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v = (f, t))

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callReject_fresh :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason),
    f.alreadyResolved = false →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r =
        ({ f with alreadyResolved := true },
          Whatwg.Ecma262.Promise.Table.settle t f.promise (Except.error r)))

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callReject_alreadyResolved :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason),
    f.alreadyResolved = true →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r = (f, t))
