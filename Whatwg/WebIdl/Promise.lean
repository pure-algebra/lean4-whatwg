import Whatwg.Ecma262

/-!
# Web IDL promise operations

Owner: the Promises section of the pinned Web IDL source, at the first packet
surface `PROMISE-PG-FIRST` freezes
(`test/contracts/promise-first-packet.contract.md`).

Landed here: "a new promise", "a promise resolved with", "a promise rejected
with", "resolve", "reject" and "mark as handled" over the `E-19`/`E-20`/`E-21`
core; "react" with its two one-sided wrappers "upon fulfillment" and "upon
rejection" (`E-31`, `E-37`, generalize; `G-11` steps 8 to 10, with an empty
handler admitted); and "wait for all" as the settled predicate `E-55`/`E-56`
already are plus the ordered result and first-rejection short-circuit `G-06`
names (decision 10).

Still open, with their gap ids: "get a promise to wait for all"
(`op.waiting-for-all-promise`, 354881..356058) and its
`[=Queue a microtask=]` step, so no ordering claim about that operation is
made here (`G-06` remainder); the returned promise of `wait for all`; the
binding layer, which stays `hostOnly` at the boundary.

Every operation is a thin wrapper over `Whatwg.Ecma262.Promise`: this module
mints no state of its own. Layering (DB-11): it imports `Whatwg.Ecma262` and
nothing else.
-/

namespace Whatwg.WebIdl

/-! ## The three allocating operations

`E-19` (generalize) supplies the ES2026 core: `Writable.freshPromise` already
is `NewPromiseCapability(%Promise%)` restricted to the intrinsic constructor,
followed immediately by `FulfillPromise`/`RejectPromise` when a settled outcome
is supplied. `G-03` supplied the capability record itself. -/

/-- `op.a-new-promise` (347604..347946), 18 Streams invocations. -/
def Promise.newPromise {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) :
    Whatwg.Ecma262.Promise.Table value reason × Nat :=
  Whatwg.Ecma262.Promise.Table.fresh t Whatwg.Ecma262.Promise.State.pending

/-- `op.a-promise-resolved-with` (347948..348631), 46 Streams invocations. -/
def Promise.resolvedWith {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value) :
    Whatwg.Ecma262.Promise.Table value reason × Nat :=
  Whatwg.Ecma262.Promise.Table.fresh t (Whatwg.Ecma262.Promise.State.fulfilled v)

/-- `op.a-promise-rejected-with` (348633..349214), 46 Streams invocations. -/
def Promise.rejectedWith {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason) :
    Whatwg.Ecma262.Promise.Table value reason × Nat :=
  Whatwg.Ecma262.Promise.Table.fresh t (Whatwg.Ecma262.Promise.State.rejected r)

/-! ## The two settling operations and the handled bit -/

/-- `op.resolve` (349216..349783), 35 Streams invocations. `E-20` (generalize). -/
def Promise.resolve {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat) (v : value) :
    Whatwg.Ecma262.Promise.Table value reason :=
  Whatwg.Ecma262.Promise.Table.settle t id (Except.ok v)

/-- `op.reject` (349785..350073), 23 Streams invocations. `E-20` (generalize). -/
def Promise.reject {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat) (r : reason) :
    Whatwg.Ecma262.Promise.Table value reason :=
  Whatwg.Ecma262.Promise.Table.settle t id (Except.error r)

/-- `op.mark-a-promise-as-handled` (356060..356713). `E-21` (generalize). R-P4
keeps the census row an uncovered denominator row because the pinned Streams
*source* invokes it zero times; the Streams *model* implements it at two call
sites, so this packet must not declare it absent. This declaration is not a
coverage witness. -/
def Promise.markAsHandled {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat) :
    Whatwg.Ecma262.Promise.Table value reason :=
  Whatwg.Ecma262.Promise.Table.markHandled t id

/-! ## `react` and the two one-sided wrappers

`E-31`, `E-37` (generalize): `Transform.subscribe` and `Writable.attachSink`
are two independently written instances of the same `PerformPromiseThen`
steps 8 to 10 case split. The general operation keeps `E-31`'s `Option`
result: a missing cell has no transition. It returns no derived promise; that
remainder is `G-11` and is `Whatwg.Ecma262.Promise.performPromiseThen`. -/

/-- `op.dfn-perform-steps-once-promise-is-settled` (350075..352408), 8 Streams
invocations. Step 7 performs `PerformPromiseThen`, so this operation **is**
`Whatwg.Ecma262.Promise.performPromiseThen` at this surface with the capability
forgotten, and it inherits step 12 — set `[[PromiseIsHandled]]` on every branch
— and steps 10 and 11 — the settled branches append to no list and hand the
captured record to the caller (Q3b findings F1 and F2, WS-PROM-CE-023 and
WS-PROM-CE-024).

Step 6's `newCapability` and step 8's `Return |newCapability|` stay out: the
derived promise is `G-11`'s remainder, so `react` still takes no capability
argument and supplies `none`. `E-31`, `E-37` (generalize). -/
def Promise.react {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body) :
    Option (Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)) :=
  (Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected none).map
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1))

/-- `op.upon-fulfillment` (352410..352816), 9 Streams invocations: `react` with
the rejection handler empty. The `none` is a `G-11` modelling restriction, not
the pinned text — REACT steps 1 to 4 build both handlers unconditionally, and
the addendum corrects §4.6's citation: the `~empty~` handler comes from
`op.performpromisethen` steps 3 and 5, the `IsCallable` test (WS-PROM-CE-036). -/
def Promise.uponFulfillment {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body) :
    Option (Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)) :=
  Promise.react t rs q promise (some steps) none

/-- `op.upon-rejection` (352818..353237), 11 Streams invocations. -/
def Promise.uponRejection {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body) :
    Option (Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)) :=
  Promise.react t rs q promise none (some steps)

/-! ## `wait for all`

Decision 10 puts both `E-55`/`E-56` rows and `op.wait-for-all` itself in this
module. `E-55` warns that calling the predicate "wait for all" overclaims, so
the predicate and the operation are separate names with separate laws. -/

/-- `E-55` (generalize): the settled predicate in `Prop` form, of which
`Piping.WritesSettled` is the Streams instance. -/
def Promise.AllSettled {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat) : Prop :=
  ∀ id ∈ ids,
    (∃ v : value, Whatwg.Ecma262.Promise.Table.get t id =
      some (Whatwg.Ecma262.Promise.State.fulfilled v)) ∨
    (∃ r : reason, Whatwg.Ecma262.Promise.Table.get t id =
      some (Whatwg.Ecma262.Promise.State.rejected r))

/-- `E-56` (generalize): the same predicate in `Bool` form, of which
`Piping.allWrittenSettled` is the Streams instance. `E-56` records that the
`Prop`/`Bool` pair has no stated agreement lemma today; `allSettled_iff` is it. -/
def Promise.allSettled {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat) : Bool :=
  ids.all (fun id =>
    match Whatwg.Ecma262.Promise.Table.get t id with
    | some (Whatwg.Ecma262.Promise.State.fulfilled _) => true
    | some (Whatwg.Ecma262.Promise.State.rejected _) => true
    | _ => false)

/-- The three answers of `op.wait-for-all` before its returned promise exists.
`pending` is a live frontier (DB-07), not a failure. -/
inductive Promise.WaitResult (value reason : Type) where
  | pending
  | success (values : List value)
  | failure (reason : reason)

/-- `op.wait-for-all` (353239..354879): the ordered result list and the
first-rejection short-circuit `G-06` records as missing. The returned promise
and the `[=Queue a microtask=]` step of `op.waiting-for-all-promise` stay out
of this packet. -/
def Promise.waitForAll {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat) :
    Promise.WaitResult value reason :=
  if Promise.allSettled t ids then
    match ids.findSome? (fun id =>
      match Whatwg.Ecma262.Promise.Table.get t id with
      | some (Whatwg.Ecma262.Promise.State.rejected r) => some r
      | _ => none) with
    | some r => Promise.WaitResult.failure r
    | none =>
        Promise.WaitResult.success
          (ids.filterMap (fun id =>
            match Whatwg.Ecma262.Promise.Table.get t id with
            | some (Whatwg.Ecma262.Promise.State.fulfilled v) => some v
            | _ => none))
  else Promise.WaitResult.pending

/-! ## The Q3b fidelity addendum's operations

`test/contracts/promise-first-packet-q3b.contract.md` §7.3, answering finding
F6 and the Web IDL minors of ruling R-P20. Attacks: WS-PROM-CE-029..031 and
WS-PROM-CE-034..036. -/

/-- `op.wait-for-all` (WAITALL, 353239..354879) as the pinned steps describe it.
Its rejection handler is "1. If |rejected| is true, abort these steps. 2. Set
|rejected| to true. 3. Perform |failureSteps| given |arg|": it fires on the
first rejection **to settle**, mentions neither `fullfilledCount` nor `total`,
and therefore runs with the other promises still pending (WS-PROM-CE-029), and
the reason it reports is that entry's, not the first in argument order
(WS-PROM-CE-030). Neither is expressible over the general table, which records
what settled and not when, so the settlement order arrives as
`Whatwg.Ecma262.Promise.SettlementTrace` — a trace over the one table, never a
second one (WS-PROM-CE-031).

`waitForAll` keeps its signature and its two law statements beside this one:
`E-55` and `E-56` own the predicate half and eleven Streams call sites reach
it. `G-06`; `E-55`, `E-56` (generalize). `op.waiting-for-all-promise`
(354881..356058) and its `[=Queue a microtask=]` step stay out, so no ordering
claim is made about the returned promise. -/
def Promise.waitForAllTraced {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat) :
    Promise.WaitResult value reason :=
  match Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids with
  | some r => Promise.WaitResult.failure r
  | none => Promise.waitForAll t ids

/-- `op.a-new-promise` (NEWP, 347604..347946) step 2, `Return ?
NewPromiseCapability(|constructor|)`: the operation's result is a
PromiseCapability Record, not a promise identity (WS-PROM-CE-034). `newPromise`
keeps its landed signature — eighteen `Whatwg/Streams/**` call sites use the
identity and `E-19` (generalize) is the row it serves — and this is the form
the pinned text returns. `G-03`; NEWCAP. -/
def Promise.newPromiseWithCapability {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (functionSeed : Nat) :
    Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Capability :=
  Whatwg.Ecma262.Promise.newPromiseCapability t functionSeed

/-- `op.resolve` (RESOLVE, 349216..349783) step 3, `Perform !
Call(|p|.[[Resolve]], undefined, « |value| »)`: the operation goes through the
resolving functions and so inherits the shared one-shot marker of
`op.createresolvingfunctions`, which a direct table settle does not have
(WS-PROM-CE-035). `resolve` keeps its landed signature — `E-20` (generalize)
and 58 Streams invocations. `G-03`; RESOLVING. -/
def Promise.resolveThrough {value reason : Type}
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value) :
    Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason :=
  Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v

/-- `op.reject` (REJECTOP, 349785..350073) step 1, the same through
`[[Reject]]`. `G-03`; `E-20` (generalize), RESOLVING. -/
def Promise.rejectThrough {value reason : Type}
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason) :
    Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason :=
  Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r

/-! ## Laws — the allocating and settling operations, mask M1 -/

/-- Mask M1. -/
theorem Promise.newPromise_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) :
    Promise.newPromise t =
      Whatwg.Ecma262.Promise.Table.fresh t Whatwg.Ecma262.Promise.State.pending := rfl

/-- Mask M1. -/
theorem Promise.resolvedWith_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value) :
    Promise.resolvedWith t v =
      Whatwg.Ecma262.Promise.Table.fresh t
        (Whatwg.Ecma262.Promise.State.fulfilled v) := rfl

/-- Mask M1. -/
theorem Promise.rejectedWith_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason) :
    Promise.rejectedWith t r =
      Whatwg.Ecma262.Promise.Table.fresh t
        (Whatwg.Ecma262.Promise.State.rejected r) := rfl

/-- Mask M1. -/
theorem Promise.resolve_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat) (v : value) :
    Promise.resolve t id v =
      Whatwg.Ecma262.Promise.Table.settle t id (Except.ok v) := rfl

/-- Mask M1. -/
theorem Promise.reject_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat) (r : reason) :
    Promise.reject t id r =
      Whatwg.Ecma262.Promise.Table.settle t id (Except.error r) := rfl

/-- Mask M1. -/
theorem Promise.markAsHandled_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (id : Nat) :
    Promise.markAsHandled t id =
      Whatwg.Ecma262.Promise.Table.markHandled t id := rfl

/-! ## Laws — `react` -/

/-- The generalization of `Transform.subscribe_pending`. Q3b findings F1 and
F4: step 12 marks the promise handled on every branch, and `add` takes the
capability, which `react` supplies as `none` (step 6's `newCapability` is
`G-11`'s remainder). Mask M1. -/
theorem Promise.react_pending {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise =
        some Whatwg.Ecma262.Promise.State.pending →
      Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected none).1,
          q, none) := by
  intro h
  simp [Promise.react,
    Whatwg.Ecma262.Promise.performPromiseThen_pending t rs q promise onFulfilled onRejected
      none h]

/-- The generalization of `Transform.subscribe_fulfilled`. Q3b finding F2: the
branch appends to neither list and hands the minted record to the caller. The
enqueued job is unchanged, so the M2 content of the law is exactly what it was.
Mask M2: the statement observes the reaction job entering the queue. -/
theorem Promise.react_fulfilled {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (v : value) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.fulfilled v) →
      Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled none).1,
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.ok v)),
          some (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.fulfill onFulfilled none).2) := by
  intro h
  simp [Promise.react,
    Whatwg.Ecma262.Promise.performPromiseThen_fulfilled t rs q promise v onFulfilled onRejected
      none h]

/-- The generalization of `Transform.subscribe_rejected`, for the same finding
and the same reason. Mask M2. -/
theorem Promise.react_rejected {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (r : reason) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.rejected r) →
      Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Table.markHandled t promise,
          (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.reject onRejected none).1,
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.error r)),
          some (Whatwg.Ecma262.Promise.Reactions.mint rs promise
            Whatwg.Ecma262.Promise.ReactionType.reject onRejected none).2) := by
  intro h
  simp [Promise.react,
    Whatwg.Ecma262.Promise.performPromiseThen_rejected t rs q promise r onFulfilled onRejected
      none h]

/-- The generalization of `Transform.subscribe_missing`. `E-31` risk:
`PerformPromiseThen` is total where this is partial; the packet keeps the
Streams `Option` and records the difference rather than smoothing it.
Mask M1. -/
theorem Promise.react_missing {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise = none →
      Promise.react t rs q promise onFulfilled onRejected = none := by
  intro h
  simp [Promise.react,
    Whatwg.Ecma262.Promise.performPromiseThen_missing t rs q promise onFulfilled onRejected
      none h]

/-- Mask M1. -/
theorem Promise.uponFulfillment_eq {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body) :
    Promise.uponFulfillment t rs q promise steps =
      Promise.react t rs q promise (some steps) none := rfl

/-- Mask M1. -/
theorem Promise.uponRejection_eq {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body) :
    Promise.uponRejection t rs q promise steps =
      Promise.react t rs q promise none (some steps) := rfl

/-! ## Laws — `wait for all` -/

/-- Mask M1. -/
theorem Promise.AllSettled_iff {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat) :
    Promise.AllSettled t ids ↔
      ∀ id ∈ ids,
        (∃ v : value, Whatwg.Ecma262.Promise.Table.get t id =
          some (Whatwg.Ecma262.Promise.State.fulfilled v)) ∨
        (∃ r : reason, Whatwg.Ecma262.Promise.Table.get t id =
          some (Whatwg.Ecma262.Promise.State.rejected r)) := Iff.rfl

/-- The `Prop`/`Bool` agreement `E-56` records as absent today. Mask M1. -/
theorem Promise.allSettled_iff {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat) :
    Promise.allSettled t ids = true ↔ Promise.AllSettled t ids := by
  simp only [Promise.allSettled, Promise.AllSettled, List.all_eq_true]
  constructor
  · intro h id hid
    have hb := h id hid
    revert hb
    cases hg : Whatwg.Ecma262.Promise.Table.get t id with
    | none => intro hb; simp at hb
    | some state =>
        cases state with
        | pending => intro hb; simp at hb
        | fulfilled v => intro _; exact Or.inl ⟨v, rfl⟩
        | rejected r => intro _; exact Or.inr ⟨r, rfl⟩
  · intro h id hid
    rcases h id hid with ⟨v, hv⟩ | ⟨r, hr⟩
    · rw [hv]
    · rw [hr]

/-- Mask M1: an unsettled argument leaves the answer at the live frontier. -/
theorem Promise.waitForAll_pending {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat) :
    ¬ Promise.AllSettled t ids →
      Promise.waitForAll t ids = Promise.WaitResult.pending := by
  intro h
  have hb : Promise.allSettled t ids = false := by
    cases hs : Promise.allSettled t ids with
    | false => rfl
    | true => exact absurd ((Promise.allSettled_iff t ids).mp hs) h
  simp [Promise.waitForAll, hb]

/-- Mask **M1**, relabelled from M2 by the Q3b fidelity addendum
(`test/contracts/promise-first-packet-q3b.contract.md` §4.1, acceptance
condition 5, WS-PROM-CE-037). The result list is in argument order, which is
the ordering content of `wait for all`'s "in the same order" — but argument
order is neither a settlement order nor a queue order, and §7's rule makes a
theorem M2 only when its statement observes one of those two. The statement is
unchanged. -/
theorem Promise.waitForAll_success {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (ids : List Nat)
    (values : List value) :
    ids.length = values.length →
    (∀ p ∈ ids.zip values, Whatwg.Ecma262.Promise.Table.get t p.1 =
        some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
      Promise.waitForAll t ids = Promise.WaitResult.success values := by
  intro hlen hall
  have hsettled : Promise.allSettled t ids = true := by
    have : ∀ (l : List Nat) (vs : List value), l.length = vs.length →
        (∀ p ∈ l.zip vs, Whatwg.Ecma262.Promise.Table.get t p.1 =
          some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
        l.all (fun id =>
          match Whatwg.Ecma262.Promise.Table.get t id with
          | some (Whatwg.Ecma262.Promise.State.fulfilled _) => true
          | some (Whatwg.Ecma262.Promise.State.rejected _) => true
          | _ => false) = true := by
      intro l
      induction l with
      | nil => intro _ _ _; rfl
      | cons id rest ih =>
          intro vs hl ha
          cases vs with
          | nil => simp at hl
          | cons v vrest =>
              have hhead : Whatwg.Ecma262.Promise.Table.get t id =
                  some (Whatwg.Ecma262.Promise.State.fulfilled v) :=
                ha (id, v) (by simp [List.zip])
              have htail := ih vrest (by simpa using hl)
                (fun p hp => ha p (by simp [List.zip]; exact Or.inr hp))
              simp [hhead, htail]
    exact this ids values hlen hall
  have hnone : ids.findSome? (fun id =>
      match Whatwg.Ecma262.Promise.Table.get t id with
      | some (Whatwg.Ecma262.Promise.State.rejected r) => some r
      | _ => none) = none := by
    have : ∀ (l : List Nat) (vs : List value), l.length = vs.length →
        (∀ p ∈ l.zip vs, Whatwg.Ecma262.Promise.Table.get t p.1 =
          some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
        l.findSome? (fun id =>
          match Whatwg.Ecma262.Promise.Table.get t id with
          | some (Whatwg.Ecma262.Promise.State.rejected r) => some r
          | _ => none) = none := by
      intro l
      induction l with
      | nil => intro _ _ _; rfl
      | cons id rest ih =>
          intro vs hl ha
          cases vs with
          | nil => simp at hl
          | cons v vrest =>
              have hhead : Whatwg.Ecma262.Promise.Table.get t id =
                  some (Whatwg.Ecma262.Promise.State.fulfilled v) :=
                ha (id, v) (by simp [List.zip])
              have htail := ih vrest (by simpa using hl)
                (fun p hp => ha p (by simp [List.zip]; exact Or.inr hp))
              simp [hhead, htail]
    exact this ids values hlen hall
  have hvalues : ids.filterMap (fun id =>
      match Whatwg.Ecma262.Promise.Table.get t id with
      | some (Whatwg.Ecma262.Promise.State.fulfilled v) => some v
      | _ => none) = values := by
    have : ∀ (l : List Nat) (vs : List value), l.length = vs.length →
        (∀ p ∈ l.zip vs, Whatwg.Ecma262.Promise.Table.get t p.1 =
          some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
        l.filterMap (fun id =>
          match Whatwg.Ecma262.Promise.Table.get t id with
          | some (Whatwg.Ecma262.Promise.State.fulfilled v) => some v
          | _ => none) = vs := by
      intro l
      induction l with
      | nil => intro vs hl _; cases vs with | nil => rfl | cons _ _ => simp at hl
      | cons id rest ih =>
          intro vs hl ha
          cases vs with
          | nil => simp at hl
          | cons v vrest =>
              have hhead : Whatwg.Ecma262.Promise.Table.get t id =
                  some (Whatwg.Ecma262.Promise.State.fulfilled v) :=
                ha (id, v) (by simp [List.zip])
              have htail := ih vrest (by simpa using hl)
                (fun p hp => ha p (by simp [List.zip]; exact Or.inr hp))
              simp [hhead, htail]
    exact this ids values hlen hall
  simp [Promise.waitForAll, hsettled, hnone, hvalues]

/-- Mask **M1**, relabelled from M2 by the Q3b fidelity addendum (finding F6,
WS-PROM-CE-030, and ruling R-P20's "`waitForAll_failure`'s M2 label overstates
it"). The *first* rejection in **argument** order is the one reported, and
argument order is neither a settlement order nor a queue order. The statement
is unchanged. What `op.wait-for-all` actually says — the rejection handler
fires on the first rejection **to settle** — is `Promise.waitForAllTraced` and
its two genuinely M2 laws below. -/
theorem Promise.waitForAll_failure {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (before : List Nat) (id : Nat) (after : List Nat) (r : reason) :
    Promise.AllSettled t (before ++ id :: after) →
    (∀ earlier ∈ before, ∃ v : value, Whatwg.Ecma262.Promise.Table.get t earlier =
        some (Whatwg.Ecma262.Promise.State.fulfilled v)) →
    Whatwg.Ecma262.Promise.Table.get t id =
        some (Whatwg.Ecma262.Promise.State.rejected r) →
      Promise.waitForAll t (before ++ id :: after) =
        Promise.WaitResult.failure r := by
  intro hall hbefore hid
  have hsettled : Promise.allSettled t (before ++ id :: after) = true :=
    (Promise.allSettled_iff t (before ++ id :: after)).mpr hall
  have hfind : (before ++ id :: after).findSome? (fun x =>
      match Whatwg.Ecma262.Promise.Table.get t x with
      | some (Whatwg.Ecma262.Promise.State.rejected e) => some e
      | _ => none) = some r := by
    have : ∀ (l : List Nat),
        (∀ earlier ∈ l, ∃ v : value, Whatwg.Ecma262.Promise.Table.get t earlier =
          some (Whatwg.Ecma262.Promise.State.fulfilled v)) →
        (l ++ id :: after).findSome? (fun x =>
          match Whatwg.Ecma262.Promise.Table.get t x with
          | some (Whatwg.Ecma262.Promise.State.rejected e) => some e
          | _ => none) = some r := by
      intro l
      induction l with
      | nil => intro _; simp [hid]
      | cons head rest ih =>
          intro h
          obtain ⟨v, hv⟩ := h head (by simp)
          simp only [List.cons_append, List.findSome?_cons, hv]
          exact ih (fun e he => h e (by simp [he]))
    exact this before hbefore
  simp [Promise.waitForAll, hsettled, hfind]

/-! ## Laws — the Q3b fidelity addendum

`test/contracts/promise-first-packet-q3b.contract.md` §7.3. -/

/-- With no rejection settled and not every argument fulfilled, the answer is
the live frontier (DB-07), because `fullfilledCount` has not reached `total`
and no failure step has run. Mask M1. `G-06`, WAITALL. -/
theorem Promise.waitForAllTraced_pending {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat) :
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids = none →
    ¬ Promise.AllSettled t ids →
      Promise.waitForAllTraced t tr ids = Promise.WaitResult.pending := by
  intro hnone hall
  simp only [Promise.waitForAllTraced, hnone]
  exact Promise.waitForAll_pending t ids hall

/-- The fulfilment handler's `|result|[|promiseIndex|]` assignment makes the
result list argument-ordered, and the success steps run when the count reaches
the total. Argument order is not a settlement order, so this is M1 under §7's
rule. `G-06`, `E-55`, `E-56` (generalize), WAITALL. -/
theorem Promise.waitForAllTraced_success {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat)
    (values : List value) :
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids = none →
    ids.length = values.length →
    (∀ p ∈ ids.zip values, Whatwg.Ecma262.Promise.Table.get t p.1 =
        some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
      Promise.waitForAllTraced t tr ids = Promise.WaitResult.success values := by
  intro hnone hlen hall
  simp only [Promise.waitForAllTraced, hnone]
  exact Promise.waitForAll_success t ids values hlen hall

/-- **The F6 law.** The statement quantifies over the settlement trace, not the
argument list: the reported reason is the one of the earliest entry in
settlement order that is a rejection of an argument identity. The table does
not appear in the hypotheses at all. Mask M2. `G-06`, WAITALL. -/
theorem Promise.waitForAllTraced_failure {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (before after : Whatwg.Ecma262.Promise.SettlementTrace value reason)
    (id : Nat) (r : reason) (ids : List Nat) :
    List.contains ids id = true →
    (∀ e ∈ before, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
      Promise.waitForAllTraced t (before ++ (id, Except.error r) :: after) ids =
        Promise.WaitResult.failure r := by
  intro hid hbefore
  simp only [Promise.waitForAllTraced,
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection_hit before after id r ids hid hbefore]

/-- **The short-circuit** (WS-PROM-CE-029): the failure is reported even though
a sibling argument promise is still pending, so `AllSettled` is false and the
base packet's `waitForAll` would answer `pending`. The extra hypothesis is
deliberately unused in the conclusion — that is the content. Mask M2. `G-06`,
WAITALL. -/
theorem Promise.waitForAllTraced_failure_pending {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (before after : Whatwg.Ecma262.Promise.SettlementTrace value reason)
    (id other : Nat) (r : reason) (ids : List Nat) :
    List.contains ids id = true →
    List.contains ids other = true →
    Whatwg.Ecma262.Promise.Table.get t other =
        some Whatwg.Ecma262.Promise.State.pending →
    (∀ e ∈ before, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
      Promise.waitForAllTraced t (before ++ (id, Except.error r) :: after) ids =
        Promise.WaitResult.failure r := by
  intro hid _ _ hbefore
  exact Promise.waitForAllTraced_failure t before after id r ids hid hbefore

/-- Where the two forms agree: with no rejection in the trace, the traced
operation is the base packet's `waitForAll`, so the eleven Streams call sites
that reach the predicate half lose nothing. Mask M1. `G-06`, `E-55`, `E-56`
(generalize). -/
theorem Promise.waitForAll_traced_success_agree {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat) :
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids = none →
    (∀ id : Nat, List.contains ids id = true →
      ∃ v : value, Whatwg.Ecma262.Promise.Table.get t id =
        some (Whatwg.Ecma262.Promise.State.fulfilled v)) →
      Promise.waitForAllTraced t tr ids = Promise.waitForAll t ids := by
  intro hnone _
  simp only [Promise.waitForAllTraced, hnone]

/-- Mask M1. `G-03`; NEWP, NEWCAP. -/
theorem Promise.newPromiseWithCapability_eq {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (functionSeed : Nat) :
    Promise.newPromiseWithCapability t functionSeed =
      Whatwg.Ecma262.Promise.newPromiseCapability t functionSeed := rfl

/-- The landed identity is exactly the capability's `[[Promise]]`, so the base
packet's `newPromise` is the capability form projected and not a different
operation. Mask M1. `E-19` (generalize); NEWP, NEWCAP. -/
theorem Promise.newPromise_capability_promise {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (functionSeed : Nat) :
    (Promise.newPromise t).2 =
      (Promise.newPromiseWithCapability t functionSeed).2.promise := rfl

/-- Mask M1. `G-03`; RESOLVE, RESOLVING. -/
theorem Promise.resolveThrough_eq {value reason : Type}
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value) :
    Promise.resolveThrough f t v =
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v := rfl

/-- Mask M1. `G-03`; REJECTOP, RESOLVING. -/
theorem Promise.rejectThrough_eq {value reason : Type}
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason) :
    Promise.rejectThrough f t r =
      Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r := rfl

/-- The exact hypothesis under which the landed direct form is the pinned one:
the resolving functions have not fired yet. Without it the two differ, which is
the whole of WS-PROM-CE-035. Mask M1. `E-20` (generalize); RESOLVE. -/
theorem Promise.resolveThrough_resolve {value reason : Type}
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value) :
    f.alreadyResolved = false →
      (Promise.resolveThrough f t v).2 = Promise.resolve t f.promise v := by
  intro h
  simp [Promise.resolveThrough, Promise.resolve,
    Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve, h]

/-- Mask M1. `E-20` (generalize); REJECTOP. -/
theorem Promise.rejectThrough_reject {value reason : Type}
    (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason) :
    f.alreadyResolved = false →
      (Promise.rejectThrough f t r).2 = Promise.reject t f.promise r := by
  intro h
  simp [Promise.rejectThrough, Promise.reject,
    Whatwg.Ecma262.Promise.ResolvingFunctions.callReject, h]

/-- `react` is `PerformPromiseThen` with the capability forgotten, which is
step 7 of `op.dfn-perform-steps-once-promise-is-settled`. Mask M1. `E-31`,
`E-37` (generalize); REACT, THEN. -/
theorem Promise.react_performPromiseThen {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body) :
    Promise.react t rs q promise onFulfilled onRejected =
      (Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
        none).map (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1)) := rfl

/-- Step 12 through step 7: every branch of `react` that returns at all leaves
the promise handled, the pending branch included. Mask M1. `G-11`, `G-02`;
REACT, THEN. -/
theorem Promise.react_handled {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (res : Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)) :
    Promise.react t rs q promise onFulfilled onRejected = some res →
      (Whatwg.Ecma262.Promise.Table.getCell res.1 promise).map
        Whatwg.Ecma262.Promise.Cell.handled = some true := by
  intro h
  rw [Promise.react_performPromiseThen] at h
  cases hp : Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
      none with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some inner =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hfst : res.1 = inner.1 := by rw [← h]
      rw [hfst]
      exact Whatwg.Ecma262.Promise.performPromiseThen_handled t rs q promise onFulfilled
        onRejected none inner hp

end Whatwg.WebIdl
