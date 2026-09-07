import Whatwg.Streams.Semantics.Configuration

/-!
# Semantics.Step.lean

Owner: the labeled small-step relation over configurations: consumer calls,
foreign-boundary answers, abort signals, and the job-queue steps that need
no decision.

Spec anchors: none; the `model` section is a reading aid only.

Opened by slice Q4. Packet:
`test/contracts/configuration-ordering.contract.md`; graph
`CONFIGURATION-PG-ORDERING`.

Two stages, kept apart by decision 7: `tick` is the deterministic stage that
admits no author decision, and `decide` is the admission of one. They are
exclusive — `tick_decide_exclusive` in `Semantics/Runs.lean` — and the gate
that separates them is `authorFrontier`, except at a checkpoint, where
`scriptBegin` is the one admitted decision and `authorFrontier` is already
`false`.

Decision 6: the checkpoint dequeue is `takeSinkHead`, which removes the
matching global token and the local mailbox head through the exact
empty-control `Writable.tick`, leaves the local trace unchanged, and does not
use the append-only `liftWritable` path.
-/

namespace Whatwg.Streams.Semantics.Ordering

open Whatwg.Streams

/-! ## The pre-start admission profile and the author frontier -/

/-- Decision 3: the proved all-successful pre-start profile. Finite nonnegative
exact size returns, nested writes and observer registrations only; no
controller error, close, abort, throwing size return or exceptional sink
return. Class [A]. -/
def preStartAllowed {α ε : Type} (d : Writable.Decision α ε) : Bool :=
  match d with
  | .write _ | .queryReady | .queryClosed | .queryDesiredSize => true
  | .returnSize (.value size) =>
      !Writable.sizes.isNaN size && !Writable.sizes.isNegative size &&
        !Writable.sizes.isInfinite size
  | _ => false

/-- Where an author decision may be admitted. Class [A]. At a checkpoint no
author decision is admitted through this gate; `scriptBegin` is admitted by
`decide` directly. In the intrinsic/empty-control gap the answer is `false`,
which is decision 7: that gap admits only the deterministic `jobFinished`
step. -/
def authorFrontier {α ε : Type} (c : Config α ε) : Bool :=
  match c.active with
  | .script | .observer _ => Writable.externalFrontier c.writable
  | .intrinsic _ =>
      match c.writable.control with
      | [] => false
      | _ => Writable.externalFrontier c.writable
  | .checkpoint => false

/-! ## The dedicated checkpoint dequeue -/

/-- Decision 6. Class [A]. The token at the head of the global FIFO and the
payload at the head of the local mailbox are removed together, and only when
they name the same sink operation; the local trace is untouched, which
`takeSinkHead_canonical_tick` states by exhibiting the exact empty-control
`Writable.tick`. -/
def takeSinkHead {α ε : Type} (c : Config α ε) (token : Job) : Option (Config α ε) :=
  match c.active with
  | .checkpoint =>
      match c.writable.control with
      | [] =>
          match c.jobs with
          | [] => none
          | head :: tokens =>
              if token = head then
                match c.writable.jobs with
                | [] => none
                | payload :: mailbox =>
                    if token.kind = JobKind.sink payload.kind payload.request then
                      some { c with
                        writable := { c.writable with
                          control := [.react payload], jobs := mailbox },
                        jobs := tokens, active := .intrinsic token,
                        trace := c.trace ++ [.jobStarted token] }
                    else none
              else none
      | _ => none
  | _ => none

/-! ## The two stages -/

/-- The deterministic stage. Class [A]. With a nonempty local control stack it
drives the canonical writable calculus and lifts the result; with an empty one
it finishes an intrinsic activation, or, at a checkpoint, starts the oldest
token. -/
def tick {α ε : Type} (c : Config α ε) : Option (Config α ε) :=
  match c.writable.control with
  | [] =>
      match c.active with
      | .script => none
      | .observer _ => none
      | .intrinsic job =>
          some { c with active := .checkpoint, trace := c.trace ++ [.jobFinished job] }
      | .checkpoint =>
          match c.jobs with
          | [] => none
          | token :: rest =>
              match token.kind with
              | .startup =>
                  some { c with
                    startup := .started, jobs := rest,
                    trace := c.trace ++ [.jobStarted token, .jobFinished token] }
              | .sink _ _ => takeSinkHead c token
              | .observer id =>
                  some { setRegistrationPhase { c with jobs := rest } id
                      (.running token.serial) with
                    active := .observer token, trace := c.trace ++ [.jobStarted token] }
  | _ =>
      if Writable.externalFrontier c.writable then none
      else (Writable.tick c.writable).map (liftWritable c)

/-- The admission stage. Class [A]. -/
def decide {α ε : Type} (c : Config α ε) (d : Decision α ε) : Option (Config α ε) :=
  match d with
  | .writable wd =>
      if authorFrontier c then
        match c.startup with
        | .pending =>
            if preStartAllowed wd then (Writable.decide c.writable wd).map (liftWritable c)
            else none
        | .started => (Writable.decide c.writable wd).map (liftWritable c)
      else none
  | .observe p callback => if authorFrontier c then register c p callback else none
  | .observerReturn =>
      match c.active with
      | .observer job =>
          match c.writable.control with
          | [] =>
              match job.kind with
              | .observer id =>
                  some { setRegistrationPhase c id .done with
                    active := .checkpoint,
                    trace := c.trace ++ [.observerReturned id, .jobFinished job] }
              | _ => none
          | _ => none
      | _ => none
  | .scriptReturn =>
      match c.active with
      | .script =>
          match c.writable.control with
          | [] => some { c with active := .checkpoint, trace := c.trace ++ [.scriptReturned] }
          | _ => none
      | _ => none
  | .scriptBegin =>
      match c.active with
      | .checkpoint =>
          match c.startup, c.jobs, c.writable.control with
          | .started, [], [] =>
              some { c with active := .script, trace := c.trace ++ [.scriptEntered] }
          | _, _, _ => none
      | _ => none

/-! ## The relational face -/

/-- One labeled step: `none` is the deterministic stage, `some d` an admitted
decision. Class [A]. -/
def Step {α ε : Type} (c : Config α ε) (d : Option (Decision α ε)) (t : Config α ε) : Prop :=
  (match d with | none => tick c | some decision => decide c decision) = some t

/-- Finite derivations over a decision tape. Class [A]. -/
inductive Reaches {α ε : Type} :
    Config α ε → List (Option (Decision α ε)) → Config α ε → Prop
  | nil (s : Config α ε) : Reaches s [] s
  | cons {s mid t : Config α ε} {d : Option (Decision α ε)}
      {ds : List (Option (Decision α ε))} :
      Step s d mid → Reaches mid ds t → Reaches s (d :: ds) t

/-- A derivation that never starts at a checkpoint: one episode of the run,
between two checkpoints. Class [A]. -/
inductive EpisodePrefix {α ε : Type} :
    Config α ε → List (Option (Decision α ε)) → Config α ε → Prop
  | nil (s : Config α ε) : EpisodePrefix s [] s
  | cons {s mid t : Config α ε} {d : Option (Decision α ε)}
      {ds : List (Option (Decision α ε))} :
      s.active ≠ Active.checkpoint → Step s d mid → EpisodePrefix mid ds t →
        EpisodePrefix s (d :: ds) t

/-! ## Equations — mask M1 unless noted -/

/-- Class [A]. Mask M1. -/
theorem preStartAllowed_eq {α ε : Type} (d : Writable.Decision α ε) :
    preStartAllowed d =
      (match d with
      | .write _ | .queryReady | .queryClosed | .queryDesiredSize => true
      | .returnSize (.value size) =>
          !Writable.sizes.isNaN size && !Writable.sizes.isNegative size &&
            !Writable.sizes.isInfinite size
      | _ => false) := by
  cases d <;> first | rfl | (rename_i answer; cases answer <;> rfl)

/-- Class [A]. Mask M1. -/
theorem authorFrontier_eq {α ε : Type} (c : Config α ε) :
    authorFrontier c =
      (match c.active with
      | .script | .observer _ => Writable.externalFrontier c.writable
      | .intrinsic _ => match c.writable.control with
          | [] => false
          | _ => Writable.externalFrontier c.writable
      | .checkpoint => false) := by
  unfold authorFrontier
  cases c.active <;> rfl

/-! ### The four `tick` frontier equations -/

/-- Class [A]. Mask M1. -/
theorem tick_script_empty {α ε : Type} (c : Config α ε) :
    c.active = .script → c.writable.control = [] → tick c = none := by
  intro ha hc
  unfold tick
  rw [hc, ha]

/-- Class [A]. Mask M1. -/
theorem tick_observer_empty {α ε : Type} (c : Config α ε) (job : Job) :
    c.active = .observer job → c.writable.control = [] → tick c = none := by
  intro ha hc
  unfold tick
  rw [hc, ha]

/-- Class [A]. Decision 7: the intrinsic/empty-control gap admits no author
decision, only this deterministic step. Mask M2. -/
theorem tick_intrinsic_empty {α ε : Type} (c : Config α ε) (job : Job) :
    c.active = .intrinsic job → c.writable.control = [] →
      tick c = some { c with active := .checkpoint, trace := c.trace ++ [.jobFinished job] } := by
  intro ha hc
  unfold tick
  rw [hc, ha]

/-- Class [A]. A live foreign boundary is never stepped through. Mask M1. -/
theorem tick_nonempty_foreign {α ε : Type} (c : Config α ε) :
    c.writable.control ≠ [] → Writable.externalFrontier c.writable = true → tick c = none := by
  intro hc hf
  unfold tick
  cases hcontrol : c.writable.control with
  | nil => exact absurd hcontrol hc
  | cons _ _ => simp [hf]

/-! ### The `decide` admission equations -/

/-- Class [A]. Decision 7. Mask M1. -/
theorem decide_intrinsic_gap {α ε : Type} (c : Config α ε) (job : Job) (d : Decision α ε) :
    c.active = .intrinsic job → c.writable.control = [] → decide c d = none := by
  intro ha hc
  have hf : authorFrontier c = false := by
    unfold authorFrontier
    rw [ha, hc]
  cases d <;> unfold decide <;> simp only [hf, ha, Bool.false_eq_true, if_false]

/-- Class [A]. Mask M1. -/
theorem decide_checkpoint_writable {α ε : Type} (c : Config α ε) (d : Writable.Decision α ε) :
    c.active = .checkpoint → decide c (.writable d) = none := by
  intro ha
  have hf : authorFrontier c = false := by
    unfold authorFrontier
    rw [ha]
  unfold decide
  simp only [hf, Bool.false_eq_true, if_false]

/-- Class [A]. Mask M1. -/
theorem decide_checkpoint_observe {α ε : Type} (c : Config α ε)
    (p : Whatwg.Ecma262.Promise.Ref) (callback : Nat) :
    c.active = .checkpoint → decide c (.observe p callback) = none := by
  intro ha
  have hf : authorFrontier c = false := by
    unfold authorFrontier
    rw [ha]
  unfold decide
  simp only [hf, Bool.false_eq_true, if_false]

/-- Class [A]. Mask M2. -/
theorem decide_scriptReturn {α ε : Type} (c : Config α ε) :
    c.active = .script → c.writable.control = [] →
      decide c .scriptReturn =
        some { c with active := .checkpoint, trace := c.trace ++ [.scriptReturned] } := by
  intro ha hc
  unfold decide
  rw [ha, hc]

/-- Class [A]. Mask M2. -/
theorem decide_scriptBegin {α ε : Type} (c : Config α ε) :
    c.active = .checkpoint → c.startup = .started → c.jobs = [] → c.writable.control = [] →
      decide c .scriptBegin =
        some { c with active := .script, trace := c.trace ++ [.scriptEntered] } := by
  intro ha hs hj hc
  unfold decide
  rw [ha, hs, hj, hc]

/-- Class [A]. Mask M1. -/
theorem step_iff {α ε : Type} (c t : Config α ε) (d : Option (Decision α ε)) :
    Step c d t ↔
      (match d with
        | none => tick c
        | some decision => decide c decision) = some t := Iff.rfl

/-! ### The nine checkpoint-dequeue receipts -/

/-- Class [A]. Mask M2: the statement observes which token and which payload
leave. -/
theorem takeSinkHead_matching {α ε : Type} (c : Config α ε) (token : Job)
    (tokens : List Job) (payload : Writable.SinkJob α ε)
    (mailbox : List (Writable.SinkJob α ε)) :
    c.active = .checkpoint → c.writable.control = [] → c.jobs = token :: tokens →
      c.writable.jobs = payload :: mailbox →
      token.kind = JobKind.sink payload.kind payload.request →
      takeSinkHead c token =
        some { c with
          writable := { c.writable with control := [.react payload], jobs := mailbox },
          jobs := tokens, active := .intrinsic token, trace := c.trace ++ [.jobStarted token] } := by
  intro ha hc hj hm hk
  unfold takeSinkHead
  rw [ha, hc, hj, hm]
  simp only [hk, if_pos]

/-- Class [A]. Mask M1. -/
theorem takeSinkHead_active {α ε : Type} (c : Config α ε) (token : Job) :
    c.active ≠ .checkpoint → takeSinkHead c token = none := by
  intro ha
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint => exact absurd h ha
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl

/-- Class [A]. Mask M1. -/
theorem takeSinkHead_control {α ε : Type} (c : Config α ε) (token : Job) :
    c.writable.control ≠ [] → takeSinkHead c token = none := by
  intro hc
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint =>
      cases hcontrol : c.writable.control with
      | nil => exact absurd hcontrol hc
      | cons _ _ => rfl
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl

/-- Class [A]. Mask M1. -/
theorem takeSinkHead_empty {α ε : Type} (c : Config α ε) (token : Job) :
    c.jobs = [] → takeSinkHead c token = none := by
  intro hj
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint =>
      cases hcontrol : c.writable.control with
      | nil => rw [hj]
      | cons _ _ => rfl
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl

/-- Class [A]. Mask M1. -/
theorem takeSinkHead_not_head {α ε : Type} (c : Config α ε) (token head : Job)
    (tail : List Job) :
    c.jobs = head :: tail → token ≠ head → takeSinkHead c token = none := by
  intro hj hne
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint =>
      cases hcontrol : c.writable.control with
      | nil =>
          rw [hj]
          simp only [if_neg hne]
      | cons _ _ => rfl
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl


/-- Class [A]. Mask M1. -/
theorem takeSinkHead_empty_mailbox {α ε : Type} (c : Config α ε) (token : Job) :
    c.writable.jobs = [] → takeSinkHead c token = none := by
  intro hm
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint =>
      cases hcontrol : c.writable.control with
      | nil =>
          cases hj : c.jobs with
          | nil => rfl
          | cons head tokens =>
              by_cases hh : token = head
              · simp only [if_pos hh, hm]
              · simp only [if_neg hh]
      | cons _ _ => rfl
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl

/-- Class [A]. Mask M1. -/
theorem takeSinkHead_not_sink {α ε : Type} (c : Config α ε) (token : Job) :
    (∀ (kind : Writable.SinkKind) (request : Nat), token.kind ≠ JobKind.sink kind request) →
      takeSinkHead c token = none := by
  intro hk
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint =>
      cases hcontrol : c.writable.control with
      | nil =>
          cases hj : c.jobs with
          | nil => rfl
          | cons head tokens =>
              by_cases hh : token = head
              · cases hm : c.writable.jobs with
                | nil => simp only [if_pos hh]
                | cons payload mailbox =>
                    simp only [if_pos hh, if_neg (hk payload.kind payload.request)]
              · simp only [if_neg hh]
      | cons _ _ => rfl
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl

/-- Class [A]. Mask M1. -/
theorem takeSinkHead_wrong_key {α ε : Type} (c : Config α ε) (token : Job)
    (payload : Writable.SinkJob α ε) (tail : List (Writable.SinkJob α ε)) :
    c.writable.jobs = payload :: tail →
      token.kind ≠ JobKind.sink payload.kind payload.request →
      takeSinkHead c token = none := by
  intro hm hk
  unfold takeSinkHead
  cases h : c.active with
  | checkpoint =>
      cases hcontrol : c.writable.control with
      | nil =>
          cases hj : c.jobs with
          | nil => rfl
          | cons head tokens =>
              by_cases hh : token = head
              · simp only [if_pos hh, hm, if_neg hk]
              · simp only [if_neg hh]
      | cons _ _ => rfl
  | script => rfl
  | intrinsic _ => rfl
  | observer _ => rfl

/-- Class [A]. Decision 6: the dequeue is the exact empty-control
`Writable.tick`, and it leaves the local trace unchanged. Mask M2. -/
theorem takeSinkHead_canonical_tick {α ε : Type} (c t : Config α ε) (token : Job) :
    takeSinkHead c token = some t →
      Writable.tick c.writable = some t.writable ∧ t.writable.trace = c.writable.trace := by
  intro h
  unfold takeSinkHead at h
  cases ha : c.active with
  | script => simp [ha] at h
  | intrinsic _ => simp [ha] at h
  | observer _ => simp [ha] at h
  | checkpoint =>
      simp only [ha] at h
      cases hcontrol : c.writable.control with
      | cons _ _ => simp [hcontrol] at h
      | nil =>
          simp only [hcontrol] at h
          cases hj : c.jobs with
          | nil => simp [hj] at h
          | cons head tokens =>
              simp only [hj] at h
              by_cases hh : token = head
              · simp only [if_pos hh] at h
                cases hm : c.writable.jobs with
                | nil => simp [hm] at h
                | cons payload mailbox =>
                    simp only [hm] at h
                    by_cases hk : token.kind = JobKind.sink payload.kind payload.request
                    · simp only [if_pos hk, Option.some.injEq] at h
                      subst h
                      exact ⟨by simp [Writable.tick, hcontrol, hm], rfl⟩
                    · simp [hk] at h
              · simp [hh] at h

end Whatwg.Streams.Semantics.Ordering
