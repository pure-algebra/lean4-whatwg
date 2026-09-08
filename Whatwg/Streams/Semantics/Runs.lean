import Whatwg.Streams.Semantics.Step

/-!
# Semantics.Runs.lean

Owner: runs as finite sequences of steps against a decision tape, the
big-step face composed from them, and the fixed-fuel runner that produces
decidable evidence.

Spec anchors: none; the `model` section is a reading aid only.

Opened by slice Q4. Packet:
`test/contracts/configuration-ordering.contract.md`; graph
`CONFIGURATION-PG-ORDERING`.

Decision 8: prefix comparability is stated under a **fixed consumed external
word**, and endpoint uniqueness only at normalized frontiers (`tick c = none`).
Normalization is not completion and not promise settlement (DB-07).

R-P12's `active_episode_fifo_suffix` is `episodePrefix_jobQueue_eq` below,
stated over `Whatwg.Ecma262.Jobs.Queue` through `Semantics.Ordering.jobQueue`;
`episodePrefix_jobs_eq` is the draft's own `List` shape, retained beside it so
that no class [A] law which mentions `c.jobs` has to be restated.
-/

namespace Whatwg.Streams.Semantics.Ordering

open Whatwg.Streams

/-! ## Replay helpers -/

/-- The consumed external word of a decision tape: the admitted decisions, in
order, with the silent steps dropped. Class [A]. -/
def externalWord {α ε : Type} (labels : List (Option (Decision α ε))) : List (Decision α ε) :=
  labels.filterMap id

/-- A configuration at which the deterministic stage has nothing left to do.
Decision 8: normalization is a frontier, not a completion. Class [A]. -/
def Normalized {α ε : Type} (c : Config α ε) : Prop := tick c = none

/-- Class [A]. Mask M1. -/
theorem externalWord_eq {α ε : Type} (labels : List (Option (Decision α ε))) :
    externalWord labels = labels.filterMap id := rfl

/-- Class [A]. Mask M1. -/
theorem normalized_iff {α ε : Type} (c : Config α ε) :
    Normalized c ↔ tick c = none := Iff.rfl

/-! ## Composition of derivations -/

/-- Class [A]. Mask M1. -/
theorem reaches_append {α ε : Type} {c mid t : Config α ε}
    {left right : List (Option (Decision α ε))} :
    Reaches c left mid → Reaches mid right t → Reaches c (left ++ right) t := by
  intro hl hr
  induction hl with
  | nil _ => exact hr
  | cons hstep _ ih => exact .cons hstep (ih hr)

/-- Class [A]. An episode is a derivation. Mask M1. -/
theorem episodePrefix_reaches {α ε : Type} {c t : Config α ε}
    {labels : List (Option (Decision α ε))} :
    EpisodePrefix c labels t → Reaches c labels t := by
  intro h
  induction h with
  | nil _ => exact .nil _
  | cons _ hstep _ ih => exact .cons hstep ih

/-! ## Determinism and exclusivity -/

/-- Class [A]. The two stages are functions, so a step is determined by its
label. Mask M1. -/
theorem step_deterministic {α ε : Type} {c t u : Config α ε}
    {d : Option (Decision α ε)} :
    Step c d t → Step c d u → t = u := by
  intro h1 h2
  exact Option.some.inj (h1 ▸ h2)

/-- Class [A]. Decision 7 and the `authorFrontier` gate: where the
deterministic stage steps, no author decision is admitted. Mask M1. -/
theorem tick_decide_exclusive {α ε : Type} {c t : Config α ε} (d : Decision α ε) :
    tick c = some t → decide c d = none := by
  intro ht
  cases hcontrol : c.writable.control with
  | nil =>
      cases ha : c.active with
      | script =>
          exact absurd (ht.symm.trans (tick_script_empty c ha hcontrol)) (by simp)
      | observer job =>
          exact absurd (ht.symm.trans (tick_observer_empty c job ha hcontrol)) (by simp)
      | intrinsic job => exact decide_intrinsic_gap c job d ha hcontrol
      | checkpoint =>
          cases hj : c.jobs with
          | nil =>
              have hnone : tick c = none := by
                unfold tick
                rw [hcontrol, ha, hj]
              exact absurd (ht.symm.trans hnone) (by simp)
          | cons token rest =>
              cases d with
              | writable wd => exact decide_checkpoint_writable c wd ha
              | observe p cb => exact decide_checkpoint_observe c p cb ha
              | observerReturn => unfold decide; rw [ha]
              | scriptReturn => unfold decide; rw [ha]
              | scriptBegin => simp [decide, ha, hj]
  | cons head tail =>
      have hf : Writable.externalFrontier c.writable = false := by
        cases hfrontier : Writable.externalFrontier c.writable with
        | false => rfl
        | true =>
            have hnone : tick c = none :=
              tick_nonempty_foreign c (by rw [hcontrol]; simp) hfrontier
            exact absurd (ht.symm.trans hnone) (by simp)
      have hgate : authorFrontier c = false := by
        unfold authorFrontier
        cases c.active <;> simp [hf, hcontrol]
      cases d with
      | writable wd => simp [decide, hgate]
      | observe p cb => simp [decide, hgate]
      | observerReturn =>
          unfold decide
          cases ha : c.active <;> simp [hcontrol]
      | scriptReturn =>
          unfold decide
          cases ha : c.active <;> simp [hcontrol]
      | scriptBegin =>
          unfold decide
          cases ha : c.active <;> simp [hcontrol]

/-! ## What a step does to the owner, the trace and the token FIFO

`Grows` is the shared invariant: every step keeps the owner and only appends to
the trace. `GrowsJobs` adds the FIFO clause, which holds for every step that
does **not** start at a checkpoint — the checkpoint steps are exactly the ones
that consume a token. -/

/-- Every step keeps the owner and extends the trace. -/
private def Grows {α ε : Type} (c t : Config α ε) : Prop :=
  t.owner = c.owner ∧ ∃ suffix : List (Event α ε), t.trace = c.trace ++ suffix

/-- A step that schedules exactly the tokens its trace suffix records. -/
private def GrowsJobs {α ε : Type} (c t : Config α ε) : Prop :=
  Grows c t ∧ t.jobs = c.jobs ++ queuedJobs (t.trace.drop c.trace.length)

private theorem queuedJobs_append {α ε : Type} (l r : List (Event α ε)) :
    queuedJobs (l ++ r) = queuedJobs l ++ queuedJobs r := by
  simp [queuedJobs, List.filterMap_append]

private theorem growsJobs_refl {α ε : Type} (c : Config α ε) : GrowsJobs c c := by
  refine ⟨⟨rfl, ⟨[], by simp⟩⟩, ?_⟩
  simp [queuedJobs]

private theorem growsJobs_trans {α ε : Type} {c d e : Config α ε} :
    GrowsJobs c d → GrowsJobs d e → GrowsJobs c e := by
  rintro ⟨⟨ho1, s1, hs1⟩, hj1⟩ ⟨⟨ho2, s2, hs2⟩, hj2⟩
  have htrace : e.trace = c.trace ++ (s1 ++ s2) := by
    rw [hs2, hs1, List.append_assoc]
  refine ⟨⟨ho2.trans ho1, ⟨s1 ++ s2, htrace⟩⟩, ?_⟩
  have hd1 : d.trace.drop c.trace.length = s1 := by rw [hs1]; simp
  have hd2 : e.trace.drop d.trace.length = s2 := by rw [hs2]; simp
  have hd3 : e.trace.drop c.trace.length = s1 ++ s2 := by rw [htrace]; simp
  rw [hj2, hd2, hj1, hd1, hd3, queuedJobs_append, List.append_assoc]

/-- Appending one non-scheduling event. -/
private theorem growsJobs_log {α ε : Type} (c : Config α ε) (t : Config α ε)
    (suffix : List (Event α ε)) :
    t.owner = c.owner → t.jobs = c.jobs → t.trace = c.trace ++ suffix →
      queuedJobs suffix = [] → GrowsJobs c t := by
  intro ho hj ht hq
  refine ⟨⟨ho, ⟨suffix, ht⟩⟩, ?_⟩
  rw [hj, ht]
  simp [hq]

private theorem growsJobs_enqueueJob {α ε : Type} (c : Config α ε) (kind : JobKind) :
    GrowsJobs c (enqueueJob c kind).1 := by
  refine ⟨⟨rfl, ⟨[.jobQueued ⟨c.nextJob, kind⟩], rfl⟩⟩, ?_⟩
  show c.jobs ++ [⟨c.nextJob, kind⟩] = c.jobs ++ queuedJobs ((c.trace ++ _).drop c.trace.length)
  simp [queuedJobs]

private theorem growsJobs_setPhase {α ε : Type} (c : Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase) :
    GrowsJobs c (setRegistrationPhase c id phase) :=
  growsJobs_log c _ [] rfl rfl (by simp [setRegistrationPhase]) (by simp [queuedJobs])

private theorem growsJobs_notifyStep {α ε : Type} (acc : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat) (id : Nat) :
    GrowsJobs acc
      (match r.phase with
        | .waiting =>
            if r.promise == id then
              let queued := enqueueJob acc (.observer r.id)
              setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
            else acc
        | _ => acc) := by
  cases hp : r.phase with
  | waiting =>
      by_cases hq : (r.promise == id) = true
      · simp only [hq, if_pos]
        exact growsJobs_trans (growsJobs_enqueueJob acc _) (growsJobs_setPhase _ _ _)
      · simp only [hq, Bool.false_eq_true, if_false]
        exact growsJobs_refl acc
  | queued _ => exact growsJobs_refl acc
  | running _ => exact growsJobs_refl acc
  | done => exact growsJobs_refl acc

private theorem growsJobs_notifySettled {α ε : Type} (c : Config α ε) (id : Nat) :
    GrowsJobs c (notifySettled c id) := by
  have key : ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε),
      GrowsJobs acc (l.foldl
        (fun (acc : Config α ε) (r : Whatwg.Ecma262.Promise.Reaction Nat) =>
          match r.phase with
          | .waiting =>
              if r.promise == id then
                let queued := enqueueJob acc (.observer r.id)
                setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
              else acc
          | _ => acc) acc) := by
    intro l
    induction l with
    | nil => intro acc; exact growsJobs_refl acc
    | cons r rest ih =>
        intro acc
        rw [List.foldl_cons]
        exact growsJobs_trans (growsJobs_notifyStep acc r id) (ih _)
  unfold notifySettled
  cases hl : Writable.lookupPromise c.writable id with
  | none => exact growsJobs_refl c
  | some outcome =>
      cases outcome with
      | pending => exact growsJobs_refl c
      | fulfilled _ => exact key c.registrations c
      | rejected _ => exact key c.registrations c

private theorem growsJobs_liftWritable {α ε : Type} (c : Config α ε) (w : Writable.State α ε) :
    GrowsJobs c (liftWritable c w) := by
  have hbase : GrowsJobs c { c with writable := w } :=
    growsJobs_log c _ [] rfl rfl (by simp) (by simp [queuedJobs])
  have keyEvents : ∀ (l : List (Writable.Event α ε)) (acc : Config α ε),
      GrowsJobs acc (l.foldl
        (fun (acc : Config α ε) (event : Writable.Event α ε) =>
          let logged : Config α ε := { acc with trace := acc.trace ++ [.writable event] }
          match event with
          | .settled id _ => notifySettled logged id
          | _ => logged) acc) := by
    intro l
    induction l with
    | nil => intro acc; exact growsJobs_refl acc
    | cons event rest ih =>
        intro acc
        rw [List.foldl_cons]
        refine growsJobs_trans ?_ (ih _)
        have hlog : GrowsJobs acc { acc with trace := acc.trace ++ [Event.writable event] } :=
          growsJobs_log acc _ [Event.writable event] rfl rfl rfl (by simp [queuedJobs])
        cases event with
        | settled id result =>
            exact growsJobs_trans hlog (growsJobs_notifySettled _ id)
        | sizeCalled _ _ _ => exact hlog
        | sinkCalled _ _ => exact hlog
        | signalCalled _ _ => exact hlog
        | returned _ _ => exact hlog
        | readyRead _ _ => exact hlog
        | closedRead _ _ => exact hlog
        | desiredSizeRead _ _ => exact hlog
        | controllerReturned _ => exact hlog
  have keyJobs : ∀ (l : List (Writable.SinkJob α ε)) (acc : Config α ε),
      GrowsJobs acc (l.foldl
        (fun (acc : Config α ε) (job : Writable.SinkJob α ε) =>
          (enqueueJob acc (.sink job.kind job.request)).1) acc) := by
    intro l
    induction l with
    | nil => intro acc; exact growsJobs_refl acc
    | cons job rest ih =>
        intro acc
        rw [List.foldl_cons]
        exact growsJobs_trans (growsJobs_enqueueJob acc _) (ih _)
  unfold liftWritable
  exact growsJobs_trans hbase
    (growsJobs_trans (keyEvents _ _) (keyJobs _ _))

private theorem growsJobs_register {α ε : Type} {c t : Config α ε}
    {p : Whatwg.Ecma262.Promise.Ref} {callback : Nat} :
    register c p callback = some t → GrowsJobs c t := by
  intro h
  unfold register at h
  cases hl : lookup c p with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some outcome =>
      rw [hl] at h
      have hb : GrowsJobs c
          { c with
            registrations :=
              c.registrations ++
                [⟨c.nextObserver, p.cell, .fulfill, some callback, none, .waiting⟩],
            nextObserver := c.nextObserver + 1,
            trace := c.trace ++ [.registered c.nextObserver p callback] } :=
        growsJobs_log c _ [Event.registered c.nextObserver p callback] rfl rfl rfl
          (by simp [queuedJobs])
      cases outcome with
      | pending =>
          simp only [Option.some.injEq] at h
          subst h
          exact hb
      | fulfilled _ =>
          simp only [Option.some.injEq] at h
          subst h
          exact growsJobs_trans hb
            (growsJobs_trans (growsJobs_enqueueJob _ _) (growsJobs_setPhase _ _ _))
      | rejected _ =>
          simp only [Option.some.injEq] at h
          subst h
          exact growsJobs_trans hb
            (growsJobs_trans (growsJobs_enqueueJob _ _) (growsJobs_setPhase _ _ _))

/-- Every step keeps the owner and extends the trace; a step that does not
start at a checkpoint additionally schedules exactly the tokens its trace
suffix records. -/
private theorem step_growsJobs {α ε : Type} {c t : Config α ε}
    {d : Option (Decision α ε)} :
    Step c d t → c.active ≠ Active.checkpoint → GrowsJobs c t := by
  intro hstep ha
  cases d with
  | none =>
      unfold Step at hstep
      simp only at hstep
      unfold tick at hstep
      cases hcontrol : c.writable.control with
      | nil =>
          simp only [hcontrol] at hstep
          cases hactive : c.active with
          | script => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | observer job => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | checkpoint => exact absurd hactive ha
          | intrinsic job =>
              simp only [hactive] at hstep
              simp only [Option.some.injEq] at hstep
              subst hstep
              exact growsJobs_log c _ [Event.jobFinished job] rfl rfl rfl (by simp [queuedJobs])
      | cons head tail =>
          simp only [hcontrol] at hstep
          cases hf : Writable.externalFrontier c.writable with
          | true => simp only [hf] at hstep; exact absurd hstep (by simp)
          | false =>
              simp only [hf] at hstep
              simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at hstep
              obtain ⟨w, _, hw⟩ := hstep
              subst hw
              exact growsJobs_liftWritable c w
  | some decision =>
      unfold Step at hstep
      simp only at hstep
      cases decision with
      | writable wd =>
          unfold decide at hstep
          cases hgate : authorFrontier c with
          | false => simp only [hgate] at hstep; exact absurd hstep (by simp)
          | true =>
              simp only [hgate] at hstep
              simp only [if_pos] at hstep
              cases hstart : c.startup with
              | started =>
                  simp only [hstart] at hstep
                  simp only [Option.map_eq_some_iff] at hstep
                  obtain ⟨w, _, hw⟩ := hstep
                  subst hw
                  exact growsJobs_liftWritable c w
              | pending =>
                  simp only [hstart] at hstep
                  cases hpre : preStartAllowed wd with
                  | false => simp only [hpre] at hstep; exact absurd hstep (by simp)
                  | true =>
                      simp only [hpre] at hstep
                      simp only [if_pos, Option.map_eq_some_iff] at hstep
                      obtain ⟨w, _, hw⟩ := hstep
                      subst hw
                      exact growsJobs_liftWritable c w
      | observe p callback =>
          unfold decide at hstep
          cases hgate : authorFrontier c with
          | false => simp only [hgate] at hstep; exact absurd hstep (by simp)
          | true =>
              simp only [hgate] at hstep
              simp only [if_pos] at hstep
              exact growsJobs_register hstep
      | observerReturn =>
          unfold decide at hstep
          cases hactive : c.active with
          | script => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | intrinsic _ => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | checkpoint => exact absurd hactive ha
          | observer job =>
              simp only [hactive] at hstep
              cases hcontrol : c.writable.control with
              | cons _ _ => simp only [hcontrol] at hstep; exact absurd hstep (by simp)
              | nil =>
                  simp only [hcontrol] at hstep
                  cases hkind : job.kind with
                  | startup => simp only [hkind] at hstep; exact absurd hstep (by simp)
                  | sink _ _ => simp only [hkind] at hstep; exact absurd hstep (by simp)
                  | observer id =>
                      simp only [hkind] at hstep
                      simp only [Option.some.injEq] at hstep
                      subst hstep
                      exact growsJobs_log c _
                        [Event.observerReturned id, Event.jobFinished job] rfl rfl rfl
                        (by simp [queuedJobs])
      | scriptReturn =>
          unfold decide at hstep
          cases hactive : c.active with
          | intrinsic _ => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | observer _ => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | checkpoint => exact absurd hactive ha
          | script =>
              simp only [hactive] at hstep
              cases hcontrol : c.writable.control with
              | cons _ _ => simp only [hcontrol] at hstep; exact absurd hstep (by simp)
              | nil =>
                  simp only [hcontrol] at hstep
                  simp only [Option.some.injEq] at hstep
                  subst hstep
                  exact growsJobs_log c _ [Event.scriptReturned] rfl rfl rfl (by simp [queuedJobs])
      | scriptBegin =>
          unfold decide at hstep
          cases hactive : c.active with
          | script => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | intrinsic _ => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | observer _ => simp only [hactive] at hstep; exact absurd hstep (by simp)
          | checkpoint => exact absurd hactive ha

/-! ## The step invariants the packet states -/

/-- Class [A]. One root, one owner: no step reassigns it. Mask M1. -/
theorem step_owner {α ε : Type} {c t : Config α ε} {d : Option (Decision α ε)} :
    Step c d t → t.owner = c.owner := by
  intro hstep
  by_cases ha : c.active = Active.checkpoint
  · -- at a checkpoint the only steps are the token starts and `scriptBegin`
    cases d with
    | none =>
        unfold Step at hstep
        simp only at hstep
        unfold tick at hstep
        cases hcontrol : c.writable.control with
        | cons head tail =>
            simp only [hcontrol] at hstep
            cases hf : Writable.externalFrontier c.writable with
            | true => simp only [hf] at hstep; exact absurd hstep (by simp)
            | false =>
                simp only [hf] at hstep
                simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at hstep
                obtain ⟨w, _, hw⟩ := hstep
                subst hw
                exact (growsJobs_liftWritable c w).1.1
        | nil =>
            simp only [hcontrol, ha] at hstep
            cases hj : c.jobs with
            | nil => simp only [hj] at hstep; exact absurd hstep (by simp)
            | cons token rest =>
                simp only [hj] at hstep
                cases hkind : token.kind with
                | startup =>
                    simp only [hkind] at hstep
                    simp only [Option.some.injEq] at hstep
                    subst hstep
                    rfl
                | observer id =>
                    simp only [hkind] at hstep
                    simp only [Option.some.injEq] at hstep
                    subst hstep
                    rfl
                | sink kind request =>
                    simp only [hkind] at hstep
                    unfold takeSinkHead at hstep
                    simp only [ha, hcontrol, hj] at hstep
                    cases hm : c.writable.jobs with
                    | nil => simp only [hm] at hstep; exact absurd hstep (by simp)
                    | cons payload mailbox =>
                        simp only [hm] at hstep
                        by_cases hk : token.kind = JobKind.sink payload.kind payload.request
                        · rw [if_pos hk] at hstep
                          injection hstep with hstep
                          subst hstep
                          rfl
                        · rw [if_neg hk] at hstep; exact absurd hstep (by simp)
    | some decision =>
        unfold Step at hstep
        simp only at hstep
        cases decision with
        | writable wd => simp only [decide_checkpoint_writable c wd ha] at hstep; exact absurd hstep (by simp)
        | observe p cb => simp only [decide_checkpoint_observe c p cb ha] at hstep; exact absurd hstep (by simp)
        | observerReturn =>
            unfold decide at hstep
            simp only [ha] at hstep
            exact absurd hstep (by simp)
        | scriptReturn =>
            unfold decide at hstep
            simp only [ha] at hstep
            exact absurd hstep (by simp)
        | scriptBegin =>
            unfold decide at hstep
            simp only [ha] at hstep
            cases hstart : c.startup with
            | pending => simp only [hstart] at hstep; exact absurd hstep (by simp)
            | started =>
                simp only [hstart] at hstep
                cases hj : c.jobs with
                | cons _ _ => simp only [hj] at hstep; exact absurd hstep (by simp)
                | nil =>
                    simp only [hj] at hstep
                    cases hcontrol : c.writable.control with
                    | cons _ _ => simp only [hcontrol] at hstep; exact absurd hstep (by simp)
                    | nil =>
                        simp only [hcontrol] at hstep
                        simp only [Option.some.injEq] at hstep
                        subst hstep
                        rfl
  · exact (step_growsJobs hstep ha).1.1

/-- Class [A]. The trace is append-only across a step. Mask M2. -/
theorem step_trace_extends {α ε : Type} {c t : Config α ε} {d : Option (Decision α ε)} :
    Step c d t → ∃ suffix : List (Event α ε), t.trace = c.trace ++ suffix := by
  intro hstep
  by_cases ha : c.active = Active.checkpoint
  · cases d with
    | none =>
        unfold Step at hstep
        simp only at hstep
        unfold tick at hstep
        cases hcontrol : c.writable.control with
        | cons head tail =>
            simp only [hcontrol] at hstep
            cases hf : Writable.externalFrontier c.writable with
            | true => simp only [hf] at hstep; exact absurd hstep (by simp)
            | false =>
                simp only [hf] at hstep
                simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at hstep
                obtain ⟨w, _, hw⟩ := hstep
                subst hw
                exact (growsJobs_liftWritable c w).1.2
        | nil =>
            simp only [hcontrol, ha] at hstep
            cases hj : c.jobs with
            | nil => simp only [hj] at hstep; exact absurd hstep (by simp)
            | cons token rest =>
                simp only [hj] at hstep
                cases hkind : token.kind with
                | startup =>
                    simp only [hkind] at hstep
                    simp only [Option.some.injEq] at hstep
                    subst hstep
                    exact ⟨[.jobStarted token, .jobFinished token], rfl⟩
                | observer id =>
                    simp only [hkind] at hstep
                    simp only [Option.some.injEq] at hstep
                    subst hstep
                    exact ⟨[.jobStarted token], rfl⟩
                | sink kind request =>
                    simp only [hkind] at hstep
                    unfold takeSinkHead at hstep
                    simp only [ha, hcontrol, hj] at hstep
                    cases hm : c.writable.jobs with
                    | nil => simp only [hm] at hstep; exact absurd hstep (by simp)
                    | cons payload mailbox =>
                        simp only [hm] at hstep
                        by_cases hk : token.kind = JobKind.sink payload.kind payload.request
                        · rw [if_pos hk] at hstep
                          injection hstep with hstep
                          subst hstep
                          exact ⟨[.jobStarted token], rfl⟩
                        · rw [if_neg hk] at hstep; exact absurd hstep (by simp)
    | some decision =>
        unfold Step at hstep
        simp only at hstep
        cases decision with
        | writable wd =>
            simp only [decide_checkpoint_writable c wd ha] at hstep; exact absurd hstep (by simp)
        | observe p cb =>
            simp only [decide_checkpoint_observe c p cb ha] at hstep; exact absurd hstep (by simp)
        | observerReturn => unfold decide at hstep; simp only [ha] at hstep; exact absurd hstep (by simp)
        | scriptReturn => unfold decide at hstep; simp only [ha] at hstep; exact absurd hstep (by simp)
        | scriptBegin =>
            unfold decide at hstep
            simp only [ha] at hstep
            cases hstart : c.startup with
            | pending => simp only [hstart] at hstep; exact absurd hstep (by simp)
            | started =>
                simp only [hstart] at hstep
                cases hj : c.jobs with
                | cons _ _ => simp only [hj] at hstep; exact absurd hstep (by simp)
                | nil =>
                    simp only [hj] at hstep
                    cases hcontrol : c.writable.control with
                    | cons _ _ => simp only [hcontrol] at hstep; exact absurd hstep (by simp)
                    | nil =>
                        simp only [hcontrol] at hstep
                        simp only [Option.some.injEq] at hstep
                        subst hstep
                        exact ⟨[.scriptEntered], rfl⟩
  · exact (step_growsJobs hstep ha).1.2

/-! ## The two FIFO-suffix laws -/

/-- Class [B]. One non-checkpoint step schedules at the tail, in source order.
Mask M2. -/
theorem step_active_jobs_eq {α ε : Type} {c t : Config α ε} {d : Option (Decision α ε)} :
    Step c d t → c.active ≠ Active.checkpoint →
      t.jobs = c.jobs ++ queuedJobs (t.trace.drop c.trace.length) := by
  intro hstep ha
  exact (step_growsJobs hstep ha).2

/-- Class [B]. R-P12's `active_episode_fifo_suffix`, in the draft's `List`
shape: an old tail stays in front of everything the episode schedules, in
source order. Mask M2. -/
theorem episodePrefix_jobs_eq {α ε : Type} {c t : Config α ε}
    {labels : List (Option (Decision α ε))} :
    EpisodePrefix c labels t →
      t.jobs = c.jobs ++ queuedJobs (t.trace.drop c.trace.length) := by
  intro h
  have key : ∀ {c t : Config α ε} {labels : List (Option (Decision α ε))},
      EpisodePrefix c labels t → GrowsJobs c t := by
    intro c t labels h
    induction h with
    | nil s => exact growsJobs_refl s
    | cons hactive hstep _ ih => exact growsJobs_trans (step_growsJobs hstep hactive) ih
  exact (key h).2

/-- The Q4-owned `Jobs.Queue` form of `step_active_jobs_eq`. Mask M2. -/
theorem step_active_jobQueue_eq {α ε : Type} {c t : Config α ε}
    {d : Option (Decision α ε)} :
    Step c d t → c.active ≠ Active.checkpoint →
      jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueueAll (jobQueue c)
          (queuedJobs (t.trace.drop c.trace.length)) := by
  intro hstep ha
  simp only [jobQueue, Whatwg.Ecma262.Jobs.Queue.enqueueAll, step_active_jobs_eq hstep ha]

/-- R-P12's `active_episode_fifo_suffix`, stated over
`Whatwg.Ecma262.Jobs.Queue`: an old tail stays in front of everything the
episode schedules, in source order. This is the form the ruling requires.
Mask M2. -/
theorem episodePrefix_jobQueue_eq {α ε : Type} {c t : Config α ε}
    {labels : List (Option (Decision α ε))} :
    EpisodePrefix c labels t →
      jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueueAll (jobQueue c)
          (queuedJobs (t.trace.drop c.trace.length)) := by
  intro h
  simp only [jobQueue, Whatwg.Ecma262.Jobs.Queue.enqueueAll, episodePrefix_jobs_eq h]


/-! ## The two fixed-external-word run laws

Decision 8: prefix comparability under a fixed consumed external word, with
endpoint uniqueness only at normalized frontiers. The engine is
`tick_decide_exclusive`: at every configuration either the deterministic stage
steps and no decision is admitted, or the deterministic stage is stuck. So a
derivation is forced by its external word up to how many silent steps it has
taken, which is exactly what the two statements say. -/

private theorem reaches_nil_eq {α ε : Type} {c t : Config α ε} :
    Reaches c [] t → t = c := by
  intro h
  cases h
  rfl

private theorem reaches_cons_inv {α ε : Type} {c t : Config α ε}
    {d : Option (Decision α ε)} {ds : List (Option (Decision α ε))} :
    Reaches c (d :: ds) t → ∃ mid, Step c d mid ∧ Reaches mid ds t := by
  intro h
  cases h with
  | cons hstep hrest => exact ⟨_, hstep, hrest⟩

private theorem externalWord_nil_replicate {α ε : Type}
    (l : List (Option (Decision α ε))) :
    externalWord l = [] → l = List.replicate l.length none := by
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      cases a with
      | none =>
          have hrest : externalWord rest = [] := by simpa [externalWord] using h
          simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
          exact ih hrest
      | some d => simp [externalWord] at h

private theorem strip {α ε : Type} :
    ∀ (left right : List (Option (Decision α ε))) (c t u : Config α ε),
      Reaches c left t → Reaches c right u → externalWord left = externalWord right →
        (∃ n : Nat, Reaches t (List.replicate n none) u) ∨
          (∃ n : Nat, Reaches u (List.replicate n none) t) := by
  intro left
  induction left with
  | nil =>
      intro right c t u hl hr hw
      have ht : t = c := reaches_nil_eq hl
      subst ht
      have hnone : externalWord right = [] := hw.symm.trans rfl
      have hrep := externalWord_nil_replicate right hnone
      exact Or.inl ⟨right.length, by rw [← hrep]; exact hr⟩
  | cons d left' ih =>
      intro right c t u hl hr hw
      obtain ⟨mid, hstep, hrest⟩ := reaches_cons_inv hl
      cases d with
      | none =>
          have htick : tick c = some mid := hstep
          cases right with
          | nil =>
              have hu : u = c := reaches_nil_eq hr
              subst hu
              have hnone : externalWord (none :: left') = [] := hw.trans rfl
              have hrep := externalWord_nil_replicate (none :: left') hnone
              exact Or.inr ⟨(none :: left').length, by rw [← hrep]; exact hl⟩
          | cons e right' =>
              obtain ⟨mid', hstep', hrest'⟩ := reaches_cons_inv hr
              cases e with
              | none =>
                  have hmid : mid' = mid := step_deterministic hstep' hstep
                  subst hmid
                  refine ih right' _ t u hrest hrest' ?_
                  simpa [externalWord] using hw
              | some ee =>
                  have hnone := tick_decide_exclusive ee htick
                  have hcontra : decide c ee = some mid' := hstep'
                  rw [hnone] at hcontra
                  exact absurd hcontra (by simp)
      | some dd =>
          have hdec : decide c dd = some mid := hstep
          have htick : tick c = none := by
            cases htk : tick c with
            | none => rfl
            | some x =>
                have hnone := tick_decide_exclusive dd htk
                rw [hnone] at hdec
                exact absurd hdec (by simp)
          cases right with
          | nil => exact absurd hw (by simp [externalWord])
          | cons e right' =>
              obtain ⟨mid', hstep', hrest'⟩ := reaches_cons_inv hr
              cases e with
              | none =>
                  have hcontra : tick c = some mid' := hstep'
                  rw [htick] at hcontra
                  exact absurd hcontra (by simp)
              | some ee =>
                  have hpair : dd = ee ∧ externalWord left' = externalWord right' := by
                    simpa [externalWord] using hw
                  obtain ⟨hde, hw'⟩ := hpair
                  subst hde
                  have hmid : mid' = mid := step_deterministic hstep' hstep
                  subst hmid
                  exact ih right' _ t u hrest hrest' hw'

/-- Class [A]. Decision 8: under a fixed consumed external word two
derivations from the same configuration are comparable, and the difference is
silent steps only. Mask M2. -/
theorem fixed_external_word_prefix_comparable {α ε : Type} {c t u : Config α ε}
    {left right : List (Option (Decision α ε))} :
    Reaches c left t → Reaches c right u →
      externalWord left = externalWord right →
      (∃ n : Nat, Reaches t (List.replicate n none) u) ∨
        (∃ n : Nat, Reaches u (List.replicate n none) t) := by
  intro hl hr hw
  exact strip left right c t u hl hr hw

private theorem reaches_silent_normalized {α ε : Type} {t u : Config α ε} (n : Nat) :
    Reaches t (List.replicate n none) u → Normalized t → u = t := by
  intro h hn
  cases n with
  | zero => exact reaches_nil_eq (by simpa using h)
  | succ m =>
      rw [List.replicate_succ] at h
      obtain ⟨mid, hstep, _⟩ := reaches_cons_inv h
      have hcontra : tick t = some mid := hstep
      rw [hn] at hcontra
      exact absurd hcontra (by simp)

/-- Class [A]. Decision 8: endpoint uniqueness holds only at normalized
frontiers, and normalization is neither completion nor promise settlement.
Mask M2. -/
theorem fixed_external_word_normalized_unique {α ε : Type} {c t u : Config α ε}
    {left right : List (Option (Decision α ε))} :
    Reaches c left t → Reaches c right u →
      externalWord left = externalWord right →
      Normalized t → Normalized u → t = u := by
  intro hl hr hw hnt hnu
  rcases fixed_external_word_prefix_comparable hl hr hw with ⟨n, h⟩ | ⟨n, h⟩
  · exact (reaches_silent_normalized n h hnt).symm
  · exact reaches_silent_normalized n h hnu

end Whatwg.Streams.Semantics.Ordering
