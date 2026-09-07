import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q4 law battery: the DB-11 restatement of the held P8a
configuration-ordering draft's 54 law ascriptions, plus the twelve Q4-owned
bridging receipts the re-homing owes. 66 ascriptions.

Contract: `test/contracts/configuration-ordering.contract.md`.
Graph: `CONFIGURATION-PG-ORDERING`, `docs/CONFIGURATION-DAG.md`.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

Class marks are as in `OrderingContract.lean`: **[R]** re-homed onto a landed
`Whatwg.Ecma262` name, **[B]** bridged to one, **[A]** Streams adapter carried
over unchanged. The 45 class [A] laws below are the draft's statements
verbatim, up to the class [R] type substitutions listed in §2.4 of the
contract (`PromiseRef` → `Whatwg.Ecma262.Promise.Ref` with `.local` → `.cell`,
`ObserverPhase` → `ReactionPhase`, `Registration` → `Reaction Nat`).

`episodePrefix_jobs_eq` is R-P12's named `active_episode_fifo_suffix`
obligation. It is stated twice: once in the draft's own `List` shape, and once
over `Whatwg.Ecma262.Jobs.Queue.enqueueAll` as `episodePrefix_jobQueue_eq`,
which is the form R-P12 requires.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

/-! ## [A] Initialization -/

#check (@Semantics.Ordering.initial_eq :
  ∀ {α ε : Type} (owner : Nat) (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat),
    Semantics.Ordering.initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed =
      { owner := owner, writable := Writable.initial hwm alg promiseSeed errorSeed,
        startup := .pending, active := .script, registrations := [], nextObserver := 0,
        jobs := [⟨0, .startup⟩], nextJob := 1,
        trace := [.scriptEntered, .jobQueued ⟨0, .startup⟩] })

/-! ## [B] The owner-guarded lookup

The reuse table calls `lookup` rename-only. It is not: its statement mentions
`c.owner`, `p.owner` and the writable half, none of which is general. The
Streams equation stays, and `lookup_bridge` below joins it to the landed
`Whatwg.Ecma262.Promise.Table.get` over Q3's `Writable.promiseTable`. -/

#check (@Semantics.Ordering.lookup_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (p : Whatwg.Ecma262.Promise.Ref),
    Semantics.Ordering.lookup c p =
      (if c.owner = p.owner then Writable.lookupPromise c.writable p.cell else none))

/-! ## [B] Registration lookup and phase advance -/

#check (@Semantics.Ordering.lookupRegistration_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (id : Nat),
    Semantics.Ordering.lookupRegistration c id =
      c.registrations.find? (fun r ↦ r.id == id))

#check (@Semantics.Ordering.setRegistrationPhase_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase),
    Semantics.Ordering.setRegistrationPhase c id phase =
      { c with
        registrations :=
          c.registrations.map (fun r ↦ if r.id == id then { r with phase := phase } else r) })

/-! ## [B] Scheduling one token

The reuse table calls `enqueueJob` and `enqueueJob_eq` "direct". They are not:
`Whatwg.Ecma262.Jobs.Queue.enqueue` is a tail append and nothing else, while
this operation additionally allocates a serial from `nextJob`, advances that
cursor and emits a `jobQueued` event. `enqueueJob_queue_bridge` below carries
the queue half. -/

#check (@Semantics.Ordering.enqueueJob_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (kind : Semantics.Ordering.JobKind),
    Semantics.Ordering.enqueueJob c kind =
      ({ c with
          jobs := c.jobs ++ [⟨c.nextJob, kind⟩], nextJob := c.nextJob + 1,
          trace := c.trace ++ [.jobQueued ⟨c.nextJob, kind⟩] }, ⟨c.nextJob, kind⟩))

/-! ## [A] The pre-start admission profile and the author frontier -/

#check (@Semantics.Ordering.preStartAllowed_eq :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
    Semantics.Ordering.preStartAllowed d =
      (match d with
      | .write _ | .queryReady | .queryClosed | .queryDesiredSize => true
      | .returnSize (.value size) =>
          !Writable.sizes.isNaN size && !Writable.sizes.isNegative size &&
            !Writable.sizes.isInfinite size
      | _ => false))

#check (@Semantics.Ordering.authorFrontier_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    Semantics.Ordering.authorFrontier c =
      (match c.active with
      | .script | .observer _ => Writable.externalFrontier c.writable
      | .intrinsic _ => match c.writable.control with
          | [] => false
          | _ => Writable.externalFrontier c.writable
      | .checkpoint => false))

/-! ## [A] The four `tick` frontier equations -/

#check (@Semantics.Ordering.tick_script_empty :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    c.active = .script → c.writable.control = [] → Semantics.Ordering.tick c = none)

#check (@Semantics.Ordering.tick_observer_empty :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (job : Semantics.Ordering.Job),
    c.active = .observer job → c.writable.control = [] → Semantics.Ordering.tick c = none)

#check (@Semantics.Ordering.tick_intrinsic_empty :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (job : Semantics.Ordering.Job),
    c.active = .intrinsic job → c.writable.control = [] →
      Semantics.Ordering.tick c =
        some { c with active := .checkpoint, trace := c.trace ++ [.jobFinished job] })

#check (@Semantics.Ordering.tick_nonempty_foreign :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    c.writable.control ≠ [] → Writable.externalFrontier c.writable = true →
      Semantics.Ordering.tick c = none)

/-! ## [A] The `decide` admission equations -/

#check (@Semantics.Ordering.decide_intrinsic_gap :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (job : Semantics.Ordering.Job)
    (d : Semantics.Ordering.Decision α ε),
    c.active = .intrinsic job → c.writable.control = [] →
      Semantics.Ordering.decide c d = none)

#check (@Semantics.Ordering.decide_checkpoint_writable :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (d : Writable.Decision α ε),
    c.active = .checkpoint → Semantics.Ordering.decide c (.writable d) = none)

#check (@Semantics.Ordering.decide_checkpoint_observe :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (p : Whatwg.Ecma262.Promise.Ref)
    (callback : Nat),
    c.active = .checkpoint → Semantics.Ordering.decide c (.observe p callback) = none)

#check (@Semantics.Ordering.decide_scriptReturn :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    c.active = .script → c.writable.control = [] →
      Semantics.Ordering.decide c .scriptReturn =
        some { c with active := .checkpoint, trace := c.trace ++ [.scriptReturned] })

#check (@Semantics.Ordering.decide_scriptBegin :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    c.active = .checkpoint → c.startup = .started → c.jobs = [] →
      c.writable.control = [] →
      Semantics.Ordering.decide c .scriptBegin =
        some { c with active := .script, trace := c.trace ++ [.scriptEntered] })

/-! ## [A] The relational face -/

#check (@Semantics.Ordering.step_iff :
  ∀ {α ε : Type} (c t : Semantics.Ordering.Config α ε)
    (d : Option (Semantics.Ordering.Decision α ε)),
    Semantics.Ordering.Step c d t ↔
      (match d with
        | none => Semantics.Ordering.tick c
        | some decision => Semantics.Ordering.decide c decision) = some t)

#check (@Semantics.Ordering.reaches_append :
  ∀ {α ε : Type} {c mid t : Semantics.Ordering.Config α ε}
    {left right : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Reaches c left mid → Semantics.Ordering.Reaches mid right t →
      Semantics.Ordering.Reaches c (left ++ right) t)

#check (@Semantics.Ordering.episodePrefix_reaches :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {labels : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.EpisodePrefix c labels t → Semantics.Ordering.Reaches c labels t)

/-! ## [A] The trace filter -/

#check (@Semantics.Ordering.queuedJobs_eq :
  ∀ {α ε : Type} (trace : List (Semantics.Ordering.Event α ε)),
    Semantics.Ordering.queuedJobs trace =
      trace.filterMap (fun event ↦ match event with
        | .jobQueued job => some job
        | _ => none))

/-! ## [A] The live M2 view -/

#check (@Semantics.Ordering.m2Allowed_eq :
  ∀ {ε : Type} (event : Writable.VisibleEvent ε),
    Semantics.Ordering.m2Allowed event =
      (match event with
      | .settled _ _ | .readyRead _ _ | .closedRead _ _ | .desiredSizeRead _ _ => true
      | .returned _ _ | .controllerReturned _ => false))

#check (@Semantics.Ordering.observeLive_writable :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    c.writable.status = .writable →
      ∃ p : Semantics.Ordering.M2LivePrefix ε,
        Semantics.Ordering.observeLive c = some p ∧ p.owner = c.owner ∧
          p.events = (Writable.visibleEvents c.writable).filter Semantics.Ordering.m2Allowed)

#check (@Semantics.Ordering.observeLive_outside_profile :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    c.writable.status ≠ .writable → Semantics.Ordering.observeLive c = none)

/-! ## [B] Registration, and settlement notification

`register` is Web IDL "react" (`op.dfn-perform-steps-once-promise-is-settled`,
350075..352408) and `notifySettled` is `op.triggerpromisereactions`
(2700260..2701212), exactly as the reuse table says. The equations below are
the draft's, with `Registration` re-homed onto `Whatwg.Ecma262.Promise.Reaction
Nat`: the registered entry carries the `[[Type]]` tag `fulfill`, its handler is
`some callback` on the fulfil side, and the owner conjunct of the draft's
`notifySettled` guard is discharged by `CellsWellFormed`'s
registration-owner-equals-`c.owner` clause rather than restated per entry.

`register_reactions_bridge` and `notifySettled_reactions_bridge` carry the
reaction half onto the landed operations. Only the reaction half: the landed
operations write a `Jobs.Queue (Jobs.ReactionJob …)`, while this configuration
has one heterogeneous token queue. Q3 bridged `Writable.attachSink` on its job
queue alone for the same kind of reason. -/

#check (@Semantics.Ordering.register_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (p : Whatwg.Ecma262.Promise.Ref)
    (callback : Nat),
    Semantics.Ordering.register c p callback =
      (match Semantics.Ordering.lookup c p with
      | none => none
      | some outcome =>
          let id := c.nextObserver
          let b : Semantics.Ordering.Config α ε :=
            { c with
              registrations := c.registrations ++ [⟨id, p.cell, .fulfill, some callback, .waiting⟩],
              nextObserver := id + 1, trace := c.trace ++ [.registered id p callback] }
          match outcome with
          | .pending => some b
          | .fulfilled _ | .rejected _ =>
              let queued := Semantics.Ordering.enqueueJob b (.observer id)
              some (Semantics.Ordering.setRegistrationPhase queued.1 id (.queued queued.2.serial))))

#check (@Semantics.Ordering.notifySettled_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (id : Nat),
    Semantics.Ordering.notifySettled c id =
      (match Writable.lookupPromise c.writable id with
      | none | some .pending => c
      | some (.fulfilled _) | some (.rejected _) =>
          c.registrations.foldl
            (fun (acc : Semantics.Ordering.Config α ε)
                (r : Whatwg.Ecma262.Promise.Reaction Nat) ↦
              match r.phase with
              | .waiting =>
                  if r.promise == id then
                    let queued := Semantics.Ordering.enqueueJob acc (.observer r.id)
                    Semantics.Ordering.setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
                  else acc
              | _ => acc) c))

/-! ## [A] Lifting a canonical writable transition -/

#check (@Semantics.Ordering.liftWritable_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (w : Writable.State α ε),
    Semantics.Ordering.liftWritable c w =
      (let b : Semantics.Ordering.Config α ε := { c with writable := w }
       let observed := (w.trace.drop c.writable.trace.length).foldl
         (fun (acc : Semantics.Ordering.Config α ε) (event : Writable.Event α ε) ↦
           let logged : Semantics.Ordering.Config α ε :=
             { acc with trace := acc.trace ++ [.writable event] }
           match event with
           | .settled id _ => Semantics.Ordering.notifySettled logged id
           | _ => logged) b
       (w.jobs.drop c.writable.jobs.length).foldl
         (fun (acc : Semantics.Ordering.Config α ε) (job : Writable.SinkJob α ε) ↦
           (Semantics.Ordering.enqueueJob acc (.sink job.kind job.request)).1) observed))

/-! ## [A] The dedicated checkpoint dequeue: nine receipts -/

#check (@Semantics.Ordering.takeSinkHead_matching :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job)
    (tokens : List Semantics.Ordering.Job) (payload : Writable.SinkJob α ε)
    (mailbox : List (Writable.SinkJob α ε)),
    c.active = .checkpoint → c.writable.control = [] → c.jobs = token :: tokens →
      c.writable.jobs = payload :: mailbox → token.kind = .sink payload.kind payload.request →
      Semantics.Ordering.takeSinkHead c token =
        some { c with
          writable := { c.writable with control := [.react payload], jobs := mailbox },
          jobs := tokens, active := .intrinsic token, trace := c.trace ++ [.jobStarted token] })

#check (@Semantics.Ordering.takeSinkHead_active :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job),
    c.active ≠ .checkpoint → Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_control :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job),
    c.writable.control ≠ [] → Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_empty :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job),
    c.jobs = [] → Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_not_head :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token head : Semantics.Ordering.Job)
    (tail : List Semantics.Ordering.Job),
    c.jobs = head :: tail → token ≠ head → Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_empty_mailbox :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job),
    c.writable.jobs = [] → Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_not_sink :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job),
    (∀ (kind : Writable.SinkKind) (request : Nat), token.kind ≠ .sink kind request) →
      Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_wrong_key :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job)
    (payload : Writable.SinkJob α ε) (tail : List (Writable.SinkJob α ε)),
    c.writable.jobs = payload :: tail → token.kind ≠ .sink payload.kind payload.request →
      Semantics.Ordering.takeSinkHead c token = none)

#check (@Semantics.Ordering.takeSinkHead_canonical_tick :
  ∀ {α ε : Type} (c t : Semantics.Ordering.Config α ε) (token : Semantics.Ordering.Job),
    Semantics.Ordering.takeSinkHead c token = some t →
      Writable.tick c.writable = some t.writable ∧ t.writable.trace = c.writable.trace)

/-! ## [A] The successful-control grammar -/

#check (@Semantics.Ordering.stagedRequests_nil :
  ∀ {α ε : Type}, Semantics.Ordering.stagedRequests (α := α) (ε := ε) [] = [])

#check (@Semantics.Ordering.stagedRequests_pair :
  ∀ {α ε : Type} (chunk : α) (size : Writable.Size) (call id : Nat)
    (rest : List (Writable.Control α ε)),
    Semantics.Ordering.stagedRequests
        (.enqueueWrite chunk size :: .returnPromise call id :: rest) =
      id :: Semantics.Ordering.stagedRequests rest)

#check (@Semantics.Ordering.stagedRequests_other :
  ∀ {α ε : Type} (head : Writable.Control α ε) (rest : List (Writable.Control α ε)),
    (∀ (chunk : α) (size : Writable.Size) (call id : Nat)
      (tail : List (Writable.Control α ε)),
      head :: rest ≠ .enqueueWrite chunk size :: .returnPromise call id :: tail) →
      Semantics.Ordering.stagedRequests (head :: rest) = Semantics.Ordering.stagedRequests rest)

#check (@Semantics.Ordering.sinkMarkerCount_eq :
  ∀ {α ε : Type} (control : List (Writable.Control α ε)),
    Semantics.Ordering.sinkMarkerCount control =
      (control.filter (fun frame ↦ match frame with | .awaitSink _ => true | _ => false)).length)

#check (@Semantics.Ordering.suspensions_staged_empty :
  ∀ {α ε : Type} {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest → Semantics.Ordering.stagedRequests rest = [])

#check (@Semantics.Ordering.successfulControl_advance_staged_empty :
  ∀ {α ε : Type} {rest : List (Writable.Control α ε)},
    Semantics.Ordering.SuccessfulControl (.advance :: rest) →
      Semantics.Ordering.stagedRequests (.advance :: rest) = [])

#check (@Semantics.Ordering.successfulControl_sink_at_most_one :
  ∀ {α ε : Type} {control : List (Writable.Control α ε)},
    Semantics.Ordering.SuccessfulControl control → Semantics.Ordering.sinkMarkerCount control ≤ 1)

#check (@Semantics.Ordering.suspensions_iff :
  ∀ {α ε : Type} (control : List (Writable.Control α ε)),
    Semantics.Ordering.Suspensions control ↔
      control = [] ∨
      (∃ (call : Nat) (chunk : α) (rest : List (Writable.Control α ε)),
        control = .awaitSize call chunk :: rest ∧ Semantics.Ordering.Suspensions rest) ∨
      (∃ (request : Nat) (chunk : α), control = [.awaitSink (.write request chunk)]) ∨
      (∃ (request : Nat) (chunk : α) (call id : Nat) (rest : List (Writable.Control α ε)),
        control = .awaitSink (.write request chunk) :: .returnPromise call id :: rest ∧
          Semantics.Ordering.Suspensions rest ∧ Semantics.Ordering.sinkMarkerCount rest = 0))

#check (@Semantics.Ordering.successfulControl_iff :
  ∀ {α ε : Type} (control : List (Writable.Control α ε)),
    Semantics.Ordering.SuccessfulControl control ↔
      Semantics.Ordering.Suspensions control ∨
      (∃ (call : Nat) (chunk : α) (rest : List (Writable.Control α ε)),
        control = .getSize call chunk :: rest ∧ Semantics.Ordering.Suspensions rest) ∨
      (∃ (call : Nat) (chunk : α) (size : Writable.Size) (rest : List (Writable.Control α ε)),
        control = .afterSize call chunk size :: rest ∧ Semantics.Ordering.Suspensions rest) ∨
      (∃ (chunk : α) (size : Writable.Size) (call id : Nat)
        (rest : List (Writable.Control α ε)),
        control = .enqueueWrite chunk size :: .returnPromise call id :: rest ∧
          Semantics.Ordering.Suspensions rest) ∨
      (∃ (call id : Nat) (rest : List (Writable.Control α ε)),
        control = .advance :: .returnPromise call id :: rest ∧
          Semantics.Ordering.Suspensions rest) ∨
      (∃ (call id : Nat) (rest : List (Writable.Control α ε)),
        control = .returnPromise call id :: rest ∧ Semantics.Ordering.Suspensions rest) ∨
      control = [.advance] ∨
      (∃ job : Writable.SinkJob α ε, control = [.react job]))

/-! ## [A] Replay helpers and determinism -/

#check (@Semantics.Ordering.externalWord_eq :
  ∀ {α ε : Type} (labels : List (Option (Semantics.Ordering.Decision α ε))),
    Semantics.Ordering.externalWord labels = labels.filterMap id)

#check (@Semantics.Ordering.normalized_iff :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    Semantics.Ordering.Normalized c ↔ Semantics.Ordering.tick c = none)

#check (@Semantics.Ordering.step_deterministic :
  ∀ {α ε : Type} {c t u : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)},
    Semantics.Ordering.Step c d t → Semantics.Ordering.Step c d u → t = u)

#check (@Semantics.Ordering.tick_decide_exclusive :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    (d : Semantics.Ordering.Decision α ε),
    Semantics.Ordering.tick c = some t → Semantics.Ordering.decide c d = none)

#check (@Semantics.Ordering.step_owner :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)},
    Semantics.Ordering.Step c d t → t.owner = c.owner)

#check (@Semantics.Ordering.step_trace_extends :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)},
    Semantics.Ordering.Step c d t →
      ∃ suffix : List (Semantics.Ordering.Event α ε), t.trace = c.trace ++ suffix)

/-! ## [B] The two FIFO-suffix laws

`episodePrefix_jobs_eq` is the obligation R-P12 names `active_episode_fifo_suffix`.
The `Jobs.Queue` form R-P12 requires is `episodePrefix_jobQueue_eq` below; this
pair is the draft's own `List` shape, retained so that no adapter law that
mentions `c.jobs` has to be restated. -/

#check (@Semantics.Ordering.step_active_jobs_eq :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)},
    Semantics.Ordering.Step c d t → c.active ≠ .checkpoint →
      t.jobs = c.jobs ++ Semantics.Ordering.queuedJobs (t.trace.drop c.trace.length))

#check (@Semantics.Ordering.episodePrefix_jobs_eq :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {labels : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.EpisodePrefix c labels t →
      t.jobs = c.jobs ++ Semantics.Ordering.queuedJobs (t.trace.drop c.trace.length))

/-! ## [A] The two fixed-external-word run laws -/

#check (@Semantics.Ordering.fixed_external_word_prefix_comparable :
  ∀ {α ε : Type} {c t u : Semantics.Ordering.Config α ε}
    {left right : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Reaches c left t → Semantics.Ordering.Reaches c right u →
      Semantics.Ordering.externalWord left = Semantics.Ordering.externalWord right →
      (∃ n : Nat, Semantics.Ordering.Reaches t (List.replicate n none) u) ∨
        (∃ n : Nat, Semantics.Ordering.Reaches u (List.replicate n none) t))

#check (@Semantics.Ordering.fixed_external_word_normalized_unique :
  ∀ {α ε : Type} {c t u : Semantics.Ordering.Config α ε}
    {left right : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Reaches c left t → Semantics.Ordering.Reaches c right u →
      Semantics.Ordering.externalWord left = Semantics.Ordering.externalWord right →
      Semantics.Ordering.Normalized t → Semantics.Ordering.Normalized u → t = u)

/-! ## Q4-owned bridging receipts

Twelve statements the draft does not have. They are what "re-homing" means
here: each joins one class [B] declaration to the landed name the reuse table
predicts, in the shape Q3 established for `Writable`, `Readable` and
`Transform`. None of them changes a class [A] statement. -/

/-! The configuration's token FIFO read as the landed queue. -/
#check (@Semantics.Ordering.jobQueue_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    Semantics.Ordering.jobQueue c = Whatwg.Ecma262.Jobs.Queue.mk c.jobs)

/-! Decision 8's one-list view, inverted: the draft's single registration list is
the fulfil list, and the reject list is its handler-free image. -/
#check (@Semantics.Ordering.reactions_eq :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    Semantics.Ordering.reactions c =
      Whatwg.Ecma262.Promise.Reactions.mk c.registrations
        (c.registrations.map (fun r ↦ { r with kind := .reject, handler := none }))
        c.nextObserver)

/-! The erasure onto `Whatwg.Ecma262.Jobs.Active`: the landed constructors take
a serial where this one takes the whole token, and `observer` is landed as
`job`. -/
#check (@Semantics.Ordering.activeErase_eq :
  ∀ (a : Semantics.Ordering.Active),
    Semantics.Ordering.activeErase a =
      (match a with
      | .script => .script
      | .intrinsic job => .intrinsic job.serial
      | .observer job => .job job.serial
      | .checkpoint => .checkpoint))

/-! `requirement.jobs.1` (625769..626250) and `requirement.jobs.2`
(626257..626350) reach this configuration only through the erasure. -/
#check (@Semantics.Ordering.runCondition_iff :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε),
    Whatwg.Ecma262.Jobs.RunCondition (Semantics.Ordering.activeErase c.active) ↔
      c.active = .checkpoint)

/-! `lookup` is the landed table read under the owner guard. Uses Q3's
`Writable.promiseTable` and, through it, `Writable.lookupPromise_bridge`. -/
#check (@Semantics.Ordering.lookup_bridge :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (p : Whatwg.Ecma262.Promise.Ref),
    Semantics.Ordering.lookup c p =
      (if c.owner = p.owner then
        Whatwg.Ecma262.Promise.Table.get (Writable.promiseTable c.writable) p.cell
       else none))

/-! Registration lookup is `Reactions.get` at the fulfil list. -/
#check (@Semantics.Ordering.lookupRegistration_bridge :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (id : Nat),
    Semantics.Ordering.lookupRegistration c id =
      Whatwg.Ecma262.Promise.Reactions.get (Semantics.Ordering.reactions c) .fulfill id)

/-! Phase advance is `Reactions.setPhase` at the fulfil list. -/
#check (@Semantics.Ordering.setRegistrationPhase_bridge :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase),
    (Semantics.Ordering.setRegistrationPhase c id phase).registrations =
      (Whatwg.Ecma262.Promise.Reactions.setPhase (Semantics.Ordering.reactions c)
        .fulfill id phase).fulfill)

/-! Scheduling one token is the landed tail append. -/
#check (@Semantics.Ordering.enqueueJob_queue_bridge :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (kind : Semantics.Ordering.JobKind),
    Semantics.Ordering.jobQueue (Semantics.Ordering.enqueueJob c kind).1 =
      Whatwg.Ecma262.Jobs.Queue.enqueue (Semantics.Ordering.jobQueue c)
        (Semantics.Ordering.enqueueJob c kind).2)

/-! The reaction half of `register` is Web IDL `react`'s pending branch. -/
#check (@Semantics.Ordering.register_reactions_bridge :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (p : Whatwg.Ecma262.Promise.Ref)
    (callback : Nat),
    c.owner = p.owner →
    Whatwg.Ecma262.Promise.Table.get (Writable.promiseTable c.writable) p.cell =
        some Whatwg.Ecma262.Promise.State.pending →
      (Semantics.Ordering.register c p callback).map Semantics.Ordering.reactions =
        ((Whatwg.WebIdl.Promise.react (Writable.promiseTable c.writable)
          (Semantics.Ordering.reactions c) Whatwg.Ecma262.Jobs.Queue.empty
          p.cell (some callback) none).map Prod.fst))

/-! The reaction half of `notifySettled` is `op.triggerpromisereactions`. -/
#check (@Semantics.Ordering.notifySettled_reactions_bridge :
  ∀ {α ε : Type} (c : Semantics.Ordering.Config α ε) (id : Nat),
    Writable.lookupPromise c.writable id = some (.fulfilled ()) →
      (Semantics.Ordering.notifySettled c id).registrations =
        (Whatwg.Ecma262.Promise.triggerReactions (Semantics.Ordering.reactions c) id
          .fulfill (Except.ok () : Except (Boundary.Exception ε) Unit)
          Whatwg.Ecma262.Jobs.Queue.empty).1.fulfill)

/-! One non-checkpoint step schedules at the tail, over the landed queue. -/
#check (@Semantics.Ordering.step_active_jobQueue_eq :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)},
    Semantics.Ordering.Step c d t → c.active ≠ .checkpoint →
      Semantics.Ordering.jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueueAll (Semantics.Ordering.jobQueue c)
          (Semantics.Ordering.queuedJobs (t.trace.drop c.trace.length)))

/-! R-P12's `active_episode_fifo_suffix`, stated over
`Whatwg.Ecma262.Jobs.Queue`: an old tail stays in front of everything the
episode schedules, in source order. This is the `Jobs.Queue` form of
`episodePrefix_jobs_eq` above, and it is the form the ruling requires. -/
#check (@Semantics.Ordering.episodePrefix_jobQueue_eq :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {labels : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.EpisodePrefix c labels t →
      Semantics.Ordering.jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueueAll (Semantics.Ordering.jobQueue c)
          (Semantics.Ordering.queuedJobs (t.trace.drop c.trace.length)))

/-!
Still required, unchanged from the draft: registration/notification order and
once-only proofs; source-specific ordered-effect receipts; inductive
well-formedness and successful-profile progress; arbitrary-tail FIFO and
normalized replay uniqueness; source/reference certificate erasure; the
original-start WPT derivation; retained executable mutants; and complete
theorem/axiom receipts.
-/
