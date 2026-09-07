import Whatwg.Ecma262

/-!
Breaker-owned Q3b exact-signature battery for the fidelity addendum to the
first promise packet.
Addendum: `test/contracts/promise-first-packet-q3b.contract.md`.
Base packet: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`, "Q3b addendum".
Attacks: `test/counterexamples/promise/ATTACKS.md`, WS-PROM-CE-023..038.

This module freezes the *new* `Whatwg.Ecma262.Promise` surface the six
fidelity findings F1-F6 of ruling R-P20 require. Every ascription here is
additive: it names a declaration that does not exist at `f700230`. The
ascriptions the addendum *amends* stay in the base packet's own batteries,
each with a dated addendum comment beside it, because a superseded ascription
must be readable where it was frozen.

Byte spans are 0-based, ends exclusive, into `vendor/ecma262-0248456c/spec.html`
(SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`).
Row ids are those of `generated/ecma262-census.tsv`. Citing a row id here
anchors a declaration; it moves no coverage state, and the ES2026 census stays
all-`absent`.

Every ascription names an inventory row `E-01`..`E-74` with its reuse mode or a
gap id `G-01`..`G-11` (R-P12, acceptance condition 1 of the base packet).

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## F4 — the reaction record's `[[Capability]]`

`record.promisereaction-records` (2690445..2692671, digest
`d66fc8081d7a889ffbdd77b8a4828c5ad87095a72fa04b257f808dbea8816743`) lists
`[[Capability]]` first: `field.promisereaction-records.Capability`,
2691475..2691802, digest
`67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77`, "a
PromiseCapability Record or *undefined*". `G-01` names the field as missing and
the base packet did not land it, so `op.performpromisethen`'s capability
argument was consumed by `Capability.promise` and stored nowhere, and `G-03`'s
`ResolvingFunctions` were wired to nothing (WS-PROM-CE-026).

`E-50` (`Transform.Job`, generalize, `deriving Repr` only) is the row that
constrains the repair: the new field must not force `DecidableEq` on
`Reaction`, or the general record stops being instantiable at the transform's
job payload. The `inferInstance` check below is that row's receipt. -/

#check (@Whatwg.Ecma262.Promise.Reaction.capability :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body →
    Option Whatwg.Ecma262.Promise.Capability)

/-! `E-50` (generalize): still `Repr` only, and still no `DecidableEq`. -/
#check (inferInstance :
  Repr (Whatwg.Ecma262.Promise.Reaction Nat))

/-! ## F2 — the settled branches append to no list

`op.performpromisethen` (2740635..2743669, digest
`ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce`) steps 7 and
8 create the two PromiseReaction Records; step 9, the pending branch, appends
both, one to each list; steps 10 and 11, the two settled branches, take one of
them, build a job from it and enqueue that job, and append nothing.

`Reactions.mint` is that unappended record. It consumes the shared registration
cursor, so the job it feeds carries an identity no registered reaction can
collide with, and it leaves both lists exactly as they were, so no entry is
left `waiting` on a promise that has already settled (WS-PROM-CE-024).
`G-01`; `E-29` (generalize) supplies the record. -/

#check (@Whatwg.Ecma262.Promise.Reactions.mint :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat →
    Whatwg.Ecma262.Promise.ReactionType → Option body →
    Option Whatwg.Ecma262.Promise.Capability →
    Whatwg.Ecma262.Promise.Reactions body × Whatwg.Ecma262.Promise.Reaction body)

/-! ## F3 — settling clears both reaction lists

`op.fulfillpromise` (2695419..2696230, digest
`f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e`) steps 4 and
5 and `op.rejectpromise` (2699323..2700252, digest
`1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056`) steps 4 and
5 each set **both** `[[PromiseFulfillReactions]]` and
`[[PromiseRejectReactions]]` to *undefined*, having first captured the one list
they will trigger. The base packet's `Table.settleAndTrigger` advances only the
triggered list, so a registration on the other side stays `waiting` on a
promise that can never trigger it (WS-PROM-CE-025).

`Reactions.clear` is the first-order form of "set to *undefined*": every
registration on the settled promise, in either list, leaves the `waiting`
phase. `G-01`; `E-33` (generalize) is the Streams row whose `settle_pending`
and `settle_other` receipts say nothing about it.

Both ES2026 step numberings are measured from the pinned bytes: the two
operations agree at steps 4 and 5, and ruling R-P20's "RejectPromise steps 3-4"
is corrected here in the spirit of the base packet's §11. -/

#check (@Whatwg.Ecma262.Promise.Reactions.clear :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reactions body → Nat →
    Whatwg.Ecma262.Promise.Reactions body)

/-! ## F4 — running a reaction job

`op.newpromisereactionjob` (2702885..2705591, digest
`3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b`), inner
steps 4 to 9. The Job Abstract Closure reads `[[Capability]]`, `[[Type]]` and
`[[Handler]]`; with an empty handler the result is `NormalCompletion(argument)`
for `~fulfill~` and `ThrowCompletion(argument)` for `~reject~`, and with a
handler it is `HostCallJobCallback`'s completion; then, if the capability is
not *undefined*, an abrupt result calls `[[Reject]]` and a normal result calls
`[[Resolve]]`.

DB-02 keeps the handler a first-order descriptor: the model does not run it.
`reactionHandlerResult` takes the handler's completion as a `decision` argument
on the tape and returns it unexamined when a handler is present
(WS-PROM-CE-027); when the handler is `~empty~` it returns the argument, which
already carries the `~fulfill~`/`~reject~` tag because `triggerReactions`
supplies `Except.ok v` on the fulfil side and `Except.error r` on the reject
side, so `NormalCompletion` and `ThrowCompletion` are that tag and nothing
more. `requirement.jobs.4` (626486..626589, digest
`22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b`) is why the
step is total.

`G-07`; `E-51` (`Transform.runJob`, generalize) is the Streams row whose bridge
the base packet deferred: this is the promise half of "run one job", and the
component dispatch stays in Streams. -/

#check (@Whatwg.Ecma262.Promise.reactionHandlerResult :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Reaction body →
    Except reason value → Except reason value → Except reason value)

/-! `[[Resolve]]` or `[[Reject]]` selected by the completion, through the same
one-shot marker. `G-03`; `op.createresolvingfunctions`, 2692679..2695411,
digest `8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944`. -/
#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Table value reason → Except reason value →
    Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason)

/-! `op.newpromisereactionjob` inner steps 6 to 9 as one step. It takes the
resolving functions of the capability's promise rather than minting them,
because the one-shot marker is state the configuration owns (`G-08` remainder,
P8) and a freshly minted pair would re-arm it. `G-07`, `G-03`; `E-51`
(generalize). -/
#check (@Whatwg.Ecma262.Promise.runReactionJob :
  ∀ {value reason body : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Reaction body →
    Except reason value → Except reason value →
    Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason)

/-! ## Minor — the self-resolution branch of the resolve steps

`op.createresolvingfunctions` resolve steps step 4: if
`SameValue(resolution, promise)` is *true*, reject the promise with a newly
created *TypeError* and return. The base packet's `callResolve` takes a plain
`value` and cannot see the case, because the value universe in which a promise
is one value among others is `G-04` and adoption is `G-05` (WS-PROM-CE-033).

`callResolveSelf` states the branch at the one place the model can see it: the
host supplies the resolution's promise identity. Off the self branch it answers
`none` — the `G-04`/`G-05` frontier — rather than guessing. `G-03`. -/

#check (@Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Table value reason → Nat → reason →
    Option (Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason))

/-! ## F6 — the settlement order the general table lacks

DB-04's M2 is "M1 plus the full order of promise settlements observable by the
consumer". The general table records what each identity settled *to* and not
*when*, so `op.wait-for-all`'s "the first rejection to settle" is inexpressible
over it. `SettlementTrace` is that order as first-order data: settled
identities with their outcomes, oldest first.

It is a trace, not a second table (R-P12, WS-PROM-CE-031). `Table.settleTraced`
appends one entry and returns `Table.settle`'s table unchanged, which
`Table.settleTraced_table` requires; `Table.mk`'s arity is untouched, so every
Q3 ascription over `Table` stands.

Its shape is `E-71`'s (`Whatwg.Streams.Writable.settlementTrace`, keep) lifted
off the writable event alphabet; `E-63` (`Readable.settlementTrace`, keep) is
the readable-side counterpart and its bridge is deferred with the reason the
addendum states, because the readable alphabet's `closed` entry carries no
identity. Neither Streams declaration changes in content. -/

#check (@Whatwg.Ecma262.Promise.SettlementTrace :
  Type → Type → Type)

#check (@Whatwg.Ecma262.Promise.Table.settleTraced :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.SettlementTrace value reason → Nat →
    Except reason value →
    Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.SettlementTrace value reason)

/-! The first rejection **to settle** among a list of argument identities, which
is what `op.wait-for-all`'s rejection handler fires on. `G-06`; `E-56`
(generalize) is the settled predicate that cannot express it. -/
#check (@Whatwg.Ecma262.Promise.SettlementTrace.firstRejection :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.SettlementTrace value reason →
    List Nat → Option reason)
