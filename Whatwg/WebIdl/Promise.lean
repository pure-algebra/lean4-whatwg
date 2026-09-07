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
invocations. -/
def Promise.react {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body) :
    Option (Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))) :=
  match Whatwg.Ecma262.Promise.Table.get t promise with
  | none => none
  | some Whatwg.Ecma262.Promise.State.pending =>
      some ((Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1, q)
  | some (Whatwg.Ecma262.Promise.State.fulfilled v) =>
      some (Whatwg.Ecma262.Promise.Reactions.setPhase
          (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1
          Whatwg.Ecma262.Promise.ReactionType.fulfill rs.next
          (Whatwg.Ecma262.Promise.ReactionPhase.queued rs.next),
        Whatwg.Ecma262.Jobs.Queue.enqueue q
          (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.ok v)))
  | some (Whatwg.Ecma262.Promise.State.rejected r) =>
      some (Whatwg.Ecma262.Promise.Reactions.setPhase
          (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1
          Whatwg.Ecma262.Promise.ReactionType.reject rs.next
          (Whatwg.Ecma262.Promise.ReactionPhase.queued rs.next),
        Whatwg.Ecma262.Jobs.Queue.enqueue q
          (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.error r)))

/-- `op.upon-fulfillment` (352410..352816), 9 Streams invocations: `react` with
the rejection handler empty, which is why `Reaction.handler` is `Option body`. -/
def Promise.uponFulfillment {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body) :
    Option (Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))) :=
  Promise.react t rs q promise (some steps) none

/-- `op.upon-rejection` (352818..353237), 11 Streams invocations. -/
def Promise.uponRejection {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (steps : body) :
    Option (Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue
        (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value))) :=
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

/-- The generalization of `Transform.subscribe_pending`. Mask M1. -/
theorem Promise.react_pending {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise =
        some Whatwg.Ecma262.Promise.State.pending →
      Promise.react t rs q promise onFulfilled onRejected =
        some ((Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1,
          q) := by
  intro h
  simp [Promise.react, h]

/-- The generalization of `Transform.subscribe_fulfilled`. Mask M2: the
statement observes the reaction job entering the queue. -/
theorem Promise.react_fulfilled {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (v : value) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.fulfilled v) →
      Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Reactions.setPhase
            (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1
            Whatwg.Ecma262.Promise.ReactionType.fulfill rs.next
            (Whatwg.Ecma262.Promise.ReactionPhase.queued rs.next),
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.ok v))) := by
  intro h
  simp [Promise.react, h]

/-- The generalization of `Transform.subscribe_rejected`. Mask M2. -/
theorem Promise.react_rejected {value reason body : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue
      (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (r : reason) (onFulfilled onRejected : Option body) :
    Whatwg.Ecma262.Promise.Table.get t promise =
        some (Whatwg.Ecma262.Promise.State.rejected r) →
      Promise.react t rs q promise onFulfilled onRejected =
        some (Whatwg.Ecma262.Promise.Reactions.setPhase
            (Whatwg.Ecma262.Promise.Reactions.add rs promise onFulfilled onRejected).1
            Whatwg.Ecma262.Promise.ReactionType.reject rs.next
            (Whatwg.Ecma262.Promise.ReactionPhase.queued rs.next),
          Whatwg.Ecma262.Jobs.Queue.enqueue q
            (Whatwg.Ecma262.Jobs.ReactionJob.mk rs.next (Except.error r))) := by
  intro h
  simp [Promise.react, h]

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
  simp [Promise.react, h]

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

/-- Mask M2: the result list is in argument order, which is the ordering
content of `wait for all`'s "in the same order". -/
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

/-- Mask M2: the *first* rejection in argument order is the one reported. -/
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

end Whatwg.WebIdl
