import Whatwg.Ecma262
import Whatwg.Streams

/-!
Breaker-owned Q3b law battery for the fidelity addendum to the first promise
packet.
Addendum: `test/contracts/promise-first-packet-q3b.contract.md`.
Base packet: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`, "Q3b addendum".
Attacks: `test/counterexamples/promise/ATTACKS.md`, WS-PROM-CE-023..038.

Masks (DB-04). §7 of the base packet fixes the rule and this addendum applies
it unchanged: a law whose **statement** observes the order in which settlements
happen or in which reaction jobs enter the queue is **M2**; a law that observes
only a cell value, a branch, a table shape or a terminal result is **M1**. Each
block names its mask. Argument order is neither of those two orders, which is
why the addendum relabels `waitForAll_failure` and `waitForAll_success` M1
(WS-PROM-CE-037).

`Whatwg.Streams` is imported for one bridging lemma, `E-71`'s
`Writable.settlementTrace_bridge`. No Streams definition body, theorem
statement or `attribute [local simp]` set changes for it, and
`Writable.settlementTrace`'s content is unchanged.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## F1 — `op.performpromisethen` step 12 is unconditional

Step 12, "Set _promise_.[[PromiseIsHandled]] to *true*", sits after the
three-way branch of steps 9 to 11, not inside it. The base packet's pending
branch returns the table untouched and `performPromiseThen_pending` freezes the
omission (WS-PROM-CE-023). The amended `performPromiseThen_pending` marks the
promise; the two laws below make the unconditionality checkable across all
three branches at once, so no later branch can drop it silently.
Anchors: `op.performpromisethen`, 2740635..2743669, digest
`ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce`;
`slot.PromiseIsHandled`, 2746322..2746637, digest
`c5e0730a73986eb475cb399584433d21e4aadecc069e3b2d61517937d39ed652`.
`E-21` (generalize) is the Streams row `Table.markHandled` generalizes; `G-02`
records that nothing reads the bit in this lane, and
`HostPromiseRejectionTracker` — which step 11's third sub-step calls when the
bit was *false* — stays out. -/

/-! Mask M1. `E-21` (generalize), `G-02`. -/
#check (@Whatwg.Ecma262.Promise.Table.markHandled_marked :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat),
    (Whatwg.Ecma262.Promise.Table.getCell t id).isSome = true →
      (Whatwg.Ecma262.Promise.Table.getCell
          (Whatwg.Ecma262.Promise.Table.markHandled t id) id).map
        Whatwg.Ecma262.Promise.Cell.handled = some true)

/-! Mask M1. `G-11`, step 12: every branch that returns at all leaves the
promise handled, the pending branch included. -/
#check (@Whatwg.Ecma262.Promise.performPromiseThen_handled :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability)
    (res : Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body) × Option Nat),
    Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
        capability = some res →
      (Whatwg.Ecma262.Promise.Table.getCell res.1 promise).map
        Whatwg.Ecma262.Promise.Cell.handled = some true)

/-! ## F2 — the settled branches append to no list

`op.performpromisethen` steps 10 and 11 build a job out of one of the two
records created at steps 7 and 8 and enqueue it. Neither list is touched: only
step 9's pending branch appends, and it appends one record to each. The base
packet calls `Reactions.add` on all three branches and then `setPhase` on one
of the two entries it just appended, so the opposite-side entry is left in the
`waiting` phase on a promise that has already settled — a state the pinned text
never has (WS-PROM-CE-024).
`G-01`; `E-29`, `E-31`, `E-37` (generalize). Anchor as above. -/

/-! Mask M1. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_eq :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability =
      (Whatwg.Ecma262.Promise.Reactions.mk rs.fulfill rs.reject (rs.next + 1),
        Whatwg.Ecma262.Promise.Reaction.mk rs.next promise kind handler capability
          (Whatwg.Ecma262.Promise.ReactionPhase.queued rs.next)))

/-! Mask M1: the fulfil list is not appended to. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_fulfill :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability).1.fulfill =
      rs.fulfill)

/-! Mask M1: the reject list is not appended to. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_reject :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability).1.reject =
      rs.reject)

/-! Mask M1: the shared registration cursor is still consumed, so the job the
settled branch enqueues carries an identity no registered reaction can reuse. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_next :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability).1.next =
      rs.next + 1)

/-! Mask M1: the record steps 7 and 8 create, at the settled promise's
`[[Type]]`, already queued because step 10 or 11 enqueued its job. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_reaction :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability).2 =
      Whatwg.Ecma262.Promise.Reaction.mk rs.next promise kind handler capability
        (Whatwg.Ecma262.Promise.ReactionPhase.queued rs.next))

/-! Mask M1. F4: the unappended record carries `[[Capability]]` too, which is
what `op.newpromisereactionjob` reads to resolve or reject the derived
promise. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_capability :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability),
    (Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability).2.capability =
      capability)

/-! Mask M1: the whole of F2. Minting leaves the waiting set of **every**
promise and **both** lists exactly as it was, so a settled branch can never
leave an entry waiting on a promise that has already settled. -/
#check (@Whatwg.Ecma262.Promise.Reactions.mint_no_waiting :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType) (handler : Option body)
    (capability : Option Whatwg.Ecma262.Promise.Capability) (other : Nat)
    (otherKind : Whatwg.Ecma262.Promise.ReactionType),
    Whatwg.Ecma262.Promise.Reactions.waitingOn
        (Whatwg.Ecma262.Promise.Reactions.mint rs promise kind handler capability).1
        other otherKind =
      Whatwg.Ecma262.Promise.Reactions.waitingOn rs other otherKind)

/-! ## F3 — `FulfillPromise` and `RejectPromise` clear both lists

`op.fulfillpromise` steps 4 and 5 and `op.rejectpromise` steps 4 and 5 set both
`[[PromiseFulfillReactions]]` and `[[PromiseRejectReactions]]` to *undefined*,
after step 2 has captured the one list that will be triggered. The base
packet's `Table.settleAndTrigger` advances only the triggered list, and
`triggerReactions_other_kind` — a true law about `op.triggerpromisereactions`
alone, which really does not touch the other list — reads as though the residue
were correct (WS-PROM-CE-025). That ascription keeps its statement and gains a
dated annotation; the clearing belongs to the two callers, and these laws state
it there.
Anchors: `op.fulfillpromise`, 2695419..2696230, digest
`f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e`;
`op.rejectpromise`, 2699323..2700252, digest
`1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056`.
`G-01`; `E-33` (generalize). -/

/-! Mask M1. -/
#check (@Whatwg.Ecma262.Promise.Reactions.clear_eq :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat),
    Whatwg.Ecma262.Promise.Reactions.clear rs promise =
      Whatwg.Ecma262.Promise.Reactions.mk
        (rs.fulfill.map (fun r =>
          if r.promise == promise &&
              r.phase == Whatwg.Ecma262.Promise.ReactionPhase.waiting then
            { r with phase := Whatwg.Ecma262.Promise.ReactionPhase.done }
          else r))
        (rs.reject.map (fun r =>
          if r.promise == promise &&
              r.phase == Whatwg.Ecma262.Promise.ReactionPhase.waiting then
            { r with phase := Whatwg.Ecma262.Promise.ReactionPhase.done }
          else r))
        rs.next)

/-! Mask M1: "set to *undefined*" for **both** lists, quantified over the kind
so neither side is exempt. -/
#check (@Whatwg.Ecma262.Promise.Reactions.clear_waiting :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType),
    Whatwg.Ecma262.Promise.Reactions.waitingOn
      (Whatwg.Ecma262.Promise.Reactions.clear rs promise) promise kind = [])

/-! Mask M1: clearing one promise's registrations leaves every other promise's
alone, in both lists. -/
#check (@Whatwg.Ecma262.Promise.Reactions.clear_other_promise :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise other : Nat)
    (kind : Whatwg.Ecma262.Promise.ReactionType),
    other ≠ promise →
      Whatwg.Ecma262.Promise.Reactions.waitingOn
          (Whatwg.Ecma262.Promise.Reactions.clear rs promise) other kind =
        Whatwg.Ecma262.Promise.Reactions.waitingOn rs other kind)

/-! Mask M1: clearing consumes no registration cursor. -/
#check (@Whatwg.Ecma262.Promise.Reactions.clear_next :
  ∀ {body : Type} (rs : Whatwg.Ecma262.Promise.Reactions body) (promise : Nat),
    (Whatwg.Ecma262.Promise.Reactions.clear rs promise).next = rs.next)

/-! Mask M1: the F3 law at the caller. After `FulfillPromise` or
`RejectPromise` no registration on the settled promise is waiting, in either
list. The amended `Table.settleAndTrigger_pending` gives the exact equation. -/
#check (@Whatwg.Ecma262.Promise.Table.settleAndTrigger_cleared :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value)
    (kind : Whatwg.Ecma262.Promise.ReactionType),
    Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Reactions.waitingOn
        (Whatwg.Ecma262.Promise.Table.settleAndTrigger t rs q id result).2.1 id kind = [])

/-! ## F4 — the reaction job, its capability and the handler as a decision

`op.newpromisereactionjob` (2702885..2705591, digest
`3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b`), inner
steps 4 to 9. DB-02: the handler is a first-order descriptor and the model
never runs it, so its completion arrives as a decision on the tape
(WS-PROM-CE-027). `requirement.jobs.4` (626486..626589, digest
`22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b`) is why the
step is total.
`G-07`, `G-03`; `E-51` (`Transform.runJob`, generalize) is the Streams row this
is the promise half of. -/

/-! Mask M1: inner steps 4a and 4b. With an empty handler the result is the
argument, which already carries the `~fulfill~`/`~reject~` tag `triggerReactions`
put on it, so `NormalCompletion` and `ThrowCompletion` are that tag. -/
#check (@Whatwg.Ecma262.Promise.reactionHandlerResult_empty :
  ∀ {value reason body : Type} (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value),
    reaction.handler = none →
      Whatwg.Ecma262.Promise.reactionHandlerResult reaction argument decision = argument)

/-! Mask M1: inner step 5. With a handler the result is the host's decision,
returned unexamined; nothing here models a body. -/
#check (@Whatwg.Ecma262.Promise.reactionHandlerResult_handler :
  ∀ {value reason body : Type} (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value) (h : body),
    reaction.handler = some h →
      Whatwg.Ecma262.Promise.reactionHandlerResult reaction argument decision = decision)

/-! Mask M1: a normal completion calls `[[Resolve]]`. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle_ok :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value),
    Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle f t (Except.ok v) =
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v)

/-! Mask M1: an abrupt completion calls `[[Reject]]`. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle_error :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason),
    Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle f t (Except.error r) =
      Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r)

/-! Mask M1: inner step 6. With `[[Capability]]` *undefined* the job returns
`~empty~` and settles nothing. -/
#check (@Whatwg.Ecma262.Promise.runReactionJob_no_capability :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value),
    reaction.capability = none →
      Whatwg.Ecma262.Promise.runReactionJob t f reaction argument decision = (f, t))

/-! Mask M1: an empty handler settles the capability with the argument. -/
#check (@Whatwg.Ecma262.Promise.runReactionJob_empty_handler :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value)
    (cap : Whatwg.Ecma262.Promise.Capability),
    reaction.capability = some cap → reaction.handler = none →
      Whatwg.Ecma262.Promise.runReactionJob t f reaction argument decision =
        Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle f t argument)

/-! Mask M1: inner step 9. `G-03`'s resolving functions are wired to something
at last: a normal handler result resolves the capability's promise. -/
#check (@Whatwg.Ecma262.Promise.runReactionJob_resolve :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value)
    (cap : Whatwg.Ecma262.Promise.Capability) (h : body) (v : value),
    reaction.capability = some cap → reaction.handler = some h →
    f.alreadyResolved = false → decision = Except.ok v →
      Whatwg.Ecma262.Promise.runReactionJob t f reaction argument decision =
        ({ f with alreadyResolved := true },
          Whatwg.Ecma262.Promise.Table.settle t f.promise (Except.ok v)))

/-! Mask M1: inner step 8. An abrupt handler result rejects it. -/
#check (@Whatwg.Ecma262.Promise.runReactionJob_reject :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value)
    (cap : Whatwg.Ecma262.Promise.Capability) (h : body) (r : reason),
    reaction.capability = some cap → reaction.handler = some h →
    f.alreadyResolved = false → decision = Except.error r →
      Whatwg.Ecma262.Promise.runReactionJob t f reaction argument decision =
        ({ f with alreadyResolved := true },
          Whatwg.Ecma262.Promise.Table.settle t f.promise (Except.error r)))

/-! Mask M1: the one-shot marker survives the job. A second reaction job that
reaches the same already-resolved functions settles nothing. -/
#check (@Whatwg.Ecma262.Promise.runReactionJob_once :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (reaction : Whatwg.Ecma262.Promise.Reaction body)
    (argument decision : Except reason value)
    (cap : Whatwg.Ecma262.Promise.Capability),
    reaction.capability = some cap → f.alreadyResolved = true →
      Whatwg.Ecma262.Promise.runReactionJob t f reaction argument decision = (f, t))

/-! ## Minor — the one-shot marker is shared, not per function

At this pin `op.createresolvingfunctions` (2692679..2695411, digest
`8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944`) has no
`[[AlreadyResolved]]` record. Step 1 creates one Record `{ [[Value]]: toResolve }`
that both `_resolveSteps_` (step 2) and `_rejectSteps_` (step 4) capture, and
each closure's own step 3 sets that shared `[[Value]]` to `~empty~` after its
step 1 has tested it, so calling either function disables both
(WS-PROM-CE-032). The field keeps the name `alreadyResolved` — renaming it
would break four frozen ascriptions for a citation defect — and the addendum
records the anachronism against the pinned steps. `G-03`. -/

/-! Mask M1. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve_disables_reject :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value) (r : reason),
    f.alreadyResolved = false →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callReject
          (Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v).1
          (Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v).2 r =
        ((Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v).1,
          (Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v).2))

/-! Mask M1. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callReject_disables_resolve :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason) (v : value),
    f.alreadyResolved = false →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve
          (Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r).1
          (Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r).2 v =
        ((Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r).1,
          (Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r).2))

/-! ## Minor — the self-resolution branch

`op.createresolvingfunctions` resolve steps step 4 (WS-PROM-CE-033). `G-03`,
with the `G-04` value universe and the `G-05` adoption branch still out. -/

/-! Mask M1: resolving a promise with itself rejects it, with the reason the
host allocated for the *TypeError* the step creates. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf_self :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (selfError : reason),
    f.alreadyResolved = false →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf f t f.promise selfError =
        some ({ f with alreadyResolved := true },
          Whatwg.Ecma262.Promise.Table.settle t f.promise (Except.error selfError)))

/-! Mask M1: off the self branch the operation answers `none` — the `G-04` and
`G-05` frontier — rather than guessing at a resolution it cannot inspect. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf_other :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (resolution : Nat) (selfError : reason),
    resolution ≠ f.promise →
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf f t resolution selfError =
        none)

/-! ## F6 — the settlement trace

DB-04's M2 order, as first-order data over the one table. `Table.settleTraced`
is `Table.settle` plus one appended entry; the table it returns is the same
table, which is the R-P12 receipt that no shadow table was introduced
(WS-PROM-CE-031). Anchor for the settling half: `op.fulfillpromise` and
`op.rejectpromise` as above; `E-20` (generalize). -/

/-! Mask M1: **the** no-second-table receipt. -/
#check (@Whatwg.Ecma262.Promise.Table.settleTraced_table :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (id : Nat)
    (result : Except reason value),
    (Whatwg.Ecma262.Promise.Table.settleTraced t tr id result).1 =
      Whatwg.Ecma262.Promise.Table.settle t id result)

/-! Mask M2: the statement observes the order in which settlements happen. A
settling settle appends exactly one entry, at the tail. -/
#check (@Whatwg.Ecma262.Promise.Table.settleTraced_pending :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (id : Nat)
    (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id = some Whatwg.Ecma262.Promise.State.pending →
      (Whatwg.Ecma262.Promise.Table.settleTraced t tr id result).2 = tr ++ [(id, result)])

/-! Mask M1: decision 7's guard propagates to the trace. A non-pending settle
is the identity on both components, so no identity is recorded twice. -/
#check (@Whatwg.Ecma262.Promise.Table.settleTraced_other :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (id : Nat)
    (result : Except reason value),
    Whatwg.Ecma262.Promise.Table.get t id ≠ some Whatwg.Ecma262.Promise.State.pending →
      Whatwg.Ecma262.Promise.Table.settleTraced t tr id result = (t, tr))

/-! Mask M1: the defining equation. -/
#check (@Whatwg.Ecma262.Promise.SettlementTrace.firstRejection_eq :
  ∀ {value reason : Type} (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason)
    (ids : List Nat),
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids =
      List.findSome? (fun e =>
        if List.contains ids e.1 then
          match e.2 with
          | Except.error r => some r
          | Except.ok _ => none
        else none) tr)

/-! Mask M2: the statement observes the settlement order and nothing else. The
answer is the reason of the earliest *trace* entry that is a rejection of an
argument identity, which is `op.wait-for-all`'s "first rejection to settle" and
not the first rejection in argument order (WS-PROM-CE-030). -/
#check (@Whatwg.Ecma262.Promise.SettlementTrace.firstRejection_hit :
  ∀ {value reason : Type}
    (before after : Whatwg.Ecma262.Promise.SettlementTrace value reason)
    (id : Nat) (r : reason) (ids : List Nat),
    List.contains ids id = true →
    (∀ e ∈ before, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
      Whatwg.Ecma262.Promise.SettlementTrace.firstRejection
        (before ++ (id, Except.error r) :: after) ids = some r)

/-! ## F6 — the bridge to the Streams settlement order

`E-71` (`Whatwg.Streams.Writable.settlementTrace`, keep). Its content does not
change: it is already a list of settled identities with their outcomes in
settlement order, which is exactly `SettlementTrace Unit (Boundary.Exception ε)`,
so the general first-rejection-to-settle reads off the writable settlement
order without a second projection and without a second table.

`E-63` (`Readable.settlementTrace`, keep) is the readable counterpart and its
bridge is **deferred with a stated reason**: the readable settlement alphabet's
`closed` entry carries no promise identity, so the general trace's `Nat` key is
not total over it, and supplying one would change `Readable.Settlement`, which
is a `keep` row. Mask M2. -/

#check (@Whatwg.Streams.Writable.settlementTrace_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (ids : List Nat)
    (r : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection
        (Whatwg.Streams.Writable.settlementTrace s) ids = some r →
      ∃ id : Nat, List.contains ids id = true ∧
        (id, Except.error r) ∈ Whatwg.Streams.Writable.settlementTrace s)
