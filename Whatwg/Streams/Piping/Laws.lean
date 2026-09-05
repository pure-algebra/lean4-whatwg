import Whatwg.Streams.Piping.Step

/-!
# Frozen forward-shutdown equations

PIPING-PG-FORWARD-SHUTDOWN fixes these exact requirements/candidate statements.
Local equations do not replace the general admitted-run realization proof.
The named observation stops before release and final pipe settlement.
-/

namespace Whatwg.Streams.Piping

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem deliveredReads_eq :
  ∀ {α ε : Type} (s : Readable.State α ε),
  deliveredReads s = s.trace.filterMap (fun e => match e with
    | .settled (.read id (.ok (.chunk chunk))) => some (id, chunk)
    | _ => none) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem markWrite_eq :
  ∀ {α : Type} (ls : List (ReadWriteLink α)) (id : Nat) (stage : WriteStage),
  markWrite ls id stage =
    ls.map (fun l => if l.readId = id then { l with write := stage } else l) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem writesSettled_iff :
  ∀ {α ε : Type} (s : Snapshot α ε),
  WritesSettled s ↔ ∀ l ∈ s.links, ∃ call request,
    l.write = .submitted call request ∧
      (Writable.lookupPromise s.destination request = some (.fulfilled ()) ∨
        ∃ reason, Writable.lookupPromise s.destination request = some (.rejected reason)) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem bodyDecision_iff :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
  BodyDecision d ↔ (match d with
    | .controllerError _ | .answer _ _ _ | .returnSize _ | .returnSink _ | .returnSignal => True
    | _ => False) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem readInventory_iff :
  ∀ {α ε : Type} (s : Snapshot α ε),
  ReadInventory s ↔
    s.links.map (fun l => (l.readId, l.chunk)) = deliveredReads s.source ∧
    (s.links.map ReadWriteLink.readId).Nodup := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem initialSnapshot_iff :
  ∀ {α ε : Type} (s : Snapshot α ε),
  InitialSnapshot s ↔
    ReadInventory s ∧ (∀ l ∈ s.links, l.write = .unwritten) ∧
    s.selection = none ∧ s.abortCall = none ∧ s.abortPromise = none ∧ s.finalization = none ∧
    s.source.frames = [] ∧ s.source.jobs = [] ∧ s.source.readRequests = [] ∧
    s.source.pulling = false ∧ s.source.pullAwaiting = false ∧
    (s.source.status = .readable ∨ ∃ e, s.source.status = .errored e) ∧
    ∃ hwm algorithms promiseSeed,
      s.destination = Writable.initial hwm algorithms promiseSeed s.source.nextError := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem recordAllowed_iff :
  ∀ {α ε : Type} (r : ProtocolRecord α ε),
  RecordAllowed r ↔
    let b := r.before
    let a := r.after
    b.finalization = none ∧ ReadInventory b ∧ ReadInventory a ∧
    a.preventAbort = b.preventAbort ∧ a.source.nextRead = b.source.nextRead ∧
    (match r.event with
    | .selected p =>
        b.selection = none ∧ b.source.status = .errored p.reason ∧
        p.preventAbort = b.preventAbort ∧
        (p.drainRequired = true ↔
          b.destination.status = .writable ∧ b.destination.closeState = .none) ∧
        a = { b with selection := some p }
    | .writeInvoked id chunk call =>
        b.abortCall = none ∧ b.destination.control = [] ∧ call = b.destination.nextCall ∧
        (∃ pre l post, b.links = pre ++ l :: post ∧
          (∀ earlier ∈ pre, earlier.write ≠ .unwritten) ∧
          l.readId = id ∧ l.chunk = chunk ∧ l.write = .unwritten) ∧
        (match b.selection with
          | none => b.source.status = .readable ∧ b.destination.status = .writable ∧
              b.destination.closeState = .none ∧
              ∃ size, Writable.desiredSize b.destination = some size ∧
                Readable.sizePositive size = true
          | some p => p.drainRequired = true) ∧
        Writable.decide b.destination (.write chunk) = some a.destination ∧
        a = { b with
          destination := a.destination,
          links := markWrite b.links id (.invoking call) }
    | .writeReturned id call request =>
        (∃ l ∈ b.links, l.readId = id ∧ l.write = .invoking call) ∧
        Writable.Event.returned call request ∈ b.destination.trace ∧
        (∃ outcome, Writable.lookupPromise b.destination request = some outcome) ∧
        a = { b with links := markWrite b.links id (.submitted call request) }
    | .abortInvoked call reason =>
        b.destination.control = [] ∧ b.abortCall = none ∧
        call = b.destination.nextCall ∧
        (∃ p, b.selection = some p ∧ p.preventAbort = false ∧ reason = p.reason ∧
          (p.drainRequired = false ∨ WritesSettled b)) ∧
        Writable.decide b.destination (.abort reason) = some a.destination ∧
        a = { b with destination := a.destination, abortCall := some call }
    | .abortReturned call request =>
        b.abortCall = some call ∧ b.abortPromise = none ∧
        Writable.Event.returned call request ∈ b.destination.trace ∧
        (∃ outcome, Writable.lookupPromise b.destination request = some outcome) ∧
        a = { b with abortPromise := some request }
    | .readyToFinalize reason =>
        (∃ p, b.selection = some p ∧
          (p.drainRequired = false ∨ WritesSettled b) ∧
          (if p.preventAbort then
            b.abortCall = none ∧ b.abortPromise = none ∧ reason = p.reason
          else ∃ call request, b.abortCall = some call ∧ b.abortPromise = some request ∧
            ((Writable.lookupPromise b.destination request = some (.fulfilled ()) ∧
                reason = p.reason) ∨
              Writable.lookupPromise b.destination request = some (.rejected reason)))) ∧
        a = { b with finalization := some reason }
    | .writable d =>
        (match d with | none => True | some choice => BodyDecision choice) ∧
        Writable.Step b.destination d a.destination ∧
        a = { b with destination := a.destination }
    | .sourceError reason =>
        a = { b with source := Readable.error b.source reason }
    | .administrative => a = b) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem observationChain_nil_iff :
  ∀ {α ε : Type} (a b : Snapshot α ε),
  ObservationChain a [] b ↔ a = b := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem observationChain_cons_iff :
  ∀ {α ε : Type} (a b : Snapshot α ε)
  (r : ProtocolRecord α ε) (rs : List (ProtocolRecord α ε)),
  ObservationChain a (r :: rs) b ↔
    r.before = a ∧ ObservationChain r.after rs b := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem forwardShutdownSpec_iff :
  ∀ {α ε : Type} (o : ShutdownObservation α ε),
  ForwardShutdownSpec o ↔ InitialSnapshot o.initial ∧
    ObservationChain o.initial o.records o.current ∧
    ∀ r ∈ o.records, RecordAllowed r := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem snapshot_eq :
  ∀ {α ε : Type} (s : State α ε),
  snapshot s = ⟨s.source, s.destination, s.links, s.preventAbort, s.selection,
    s.abortCall, s.abortPromise,
    match s.phase with | .readyToFinalize reason => some reason | _ => none⟩ := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem initial_eq :
  ∀ {α ε : Type} (r : Readable.State α ε) (w : Writable.State α ε) (prevent : Bool),
  initial r w prevent =
    let links := (deliveredReads r).map (fun p => ReadWriteLink.mk p.1 p.2 .unwritten)
    {
      source := r, destination := w, links := links, preventAbort := prevent,
      selection := none, abortCall := none, abortPromise := none, phase := .running,
      entry := ⟨r, w, links, prevent, none, none, none, none⟩, trace := [] } := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem observeShutdown_eq :
  ∀ {α ε : Type} (s : State α ε),
  observeShutdown s = ⟨s.entry, s.trace, snapshot s⟩ := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem emit_eq :
  ∀ {α ε : Type} (s t : State α ε) (e : ProtocolEvent α ε),
  emit s e t =
    { t with
      entry := s.entry,
      trace := s.trace ++ [⟨snapshot s, e, snapshot t⟩] } := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem drainGuard_eq :
  ∀ {α ε : Type} (w : Writable.State α ε),
  drainGuard w =
    (match w.status with | .writable => !Writable.closeQueuedOrInFlight w | _ => false) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem drainGuard_true_iff :
  ∀ {α ε : Type} (w : Writable.State α ε),
  drainGuard w = true ↔ w.status = .writable ∧ w.closeState = .none := by
  intro α ε w
  cases hs : w.status <;> cases hc : w.closeState <;>
    simp [drainGuard, Writable.closeQueuedOrInFlight, hs, hc]

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem nextUnwritten_nil :
  ∀ {α : Type},
  nextUnwritten ([] : List (ReadWriteLink α)) = none := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem nextUnwritten_cons :
  ∀ {α : Type} (l : ReadWriteLink α) (ls : List (ReadWriteLink α)),
  nextUnwritten (l :: ls) =
    (match l.write with | .unwritten => some l | _ => nextUnwritten ls) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem allWrittenSettled_eq :
  ∀ {α ε : Type} (w : Writable.State α ε) (ls : List (ReadWriteLink α)),
  allWrittenSettled w ls = ls.all (fun l =>
    match l.write with
    | .submitted _ request => match Writable.lookupPromise w request with
        | some (.fulfilled _) | some (.rejected _) => true
        | _ => false
    | _ => false) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem allWrittenSettled_iff :
  ∀ {α ε : Type} (s : Snapshot α ε),
  allWrittenSettled s.destination s.links = true ↔ WritesSettled s := by
  intro α ε s
  unfold allWrittenSettled WritesSettled
  simp only [List.all_eq_true]
  apply forall_congr'
  intro l
  apply imp_congr_right
  intro _
  cases hw : l.write with
  | unwritten => simp
  | invoking call => simp
  | submitted call request =>
      constructor
      · intro h
        refine ⟨call, request, rfl, ?_⟩
        cases hp : Writable.lookupPromise s.destination request with
        | none => simp [hp] at h
        | some outcome =>
            cases outcome with
            | pending => simp [hp] at h
            | fulfilled value => cases value; exact Or.inl rfl
            | rejected reason => exact Or.inr ⟨reason, rfl⟩
      · rintro ⟨call', request', hwrite, settled⟩
        cases hwrite
        rcases settled with hp | ⟨reason, hp⟩ <;> simp [hp]

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem lookupReturn_eq :
  ∀ {α ε : Type} (w : Writable.State α ε) (call : Nat),
  lookupReturn w call = w.trace.findSome? (fun e => match e with
    | .returned c request => if c = call then some request else none
    | _ => none) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem foreignDecision_eq :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
  foreignDecision d = (match d with
    | .controllerError _ | .answer _ _ _ | .returnSize _ | .returnSink _ | .returnSignal => true
    | _ => false) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem foreignDecision_iff :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
  foreignDecision d = true ↔ BodyDecision d := by
  intro α ε d
  cases d <;> simp [foreignDecision, BodyDecision]

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem enterForwardShutdown_eq :
  ∀ {α ε : Type} (s : State α ε),
  enterForwardShutdown s =
    (match s.selection, s.source.status with
    | none, .errored reason =>
        let p : ShutdownPlan ε := ⟨reason, drainGuard s.destination, s.preventAbort⟩
        emit s (.selected p) { s with selection := some p, phase := .draining }
    | _, _ => s) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem enterForwardShutdown_first_wins :
  ∀ {α ε : Type} (s : State α ε) (p : ShutdownPlan ε),
  s.selection = some p → enterForwardShutdown s = s := by
  intro α ε s p h
  simp [enterForwardShutdown, h]

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem invokeWrite_eq :
  ∀ {α ε : Type} (s : State α ε) (l : ReadWriteLink α),
  invokeWrite s l = (Writable.decide s.destination (.write l.chunk)).map (fun w =>
    emit s (.writeInvoked l.readId l.chunk s.destination.nextCall)
      { s with
        destination := w,
        links := markWrite s.links l.readId (.invoking s.destination.nextCall),
        phase := .returningWrite l.readId s.destination.nextCall }) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem captureWrite_eq :
  ∀ {α ε : Type} (s : State α ε) (id call : Nat),
  captureWrite s id call = (lookupReturn s.destination call).map (fun request =>
    emit s (.writeReturned id call request)
      { s with
        links := markWrite s.links id (.submitted call request),
        phase := match s.selection with | none => .running | some _ => .draining }) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem invokeAbort_eq :
  ∀ {α ε : Type} (s : State α ε) (p : ShutdownPlan ε),
  invokeAbort s p = (Writable.decide s.destination (.abort p.reason)).map (fun w =>
    emit s (.abortInvoked s.destination.nextCall p.reason)
      { s with
        destination := w, abortCall := some s.destination.nextCall,
        phase := .returningAbort s.destination.nextCall }) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem captureAbort_eq :
  ∀ {α ε : Type} (s : State α ε) (call : Nat),
  captureAbort s call = (lookupReturn s.destination call).map (fun request =>
    emit s (.abortReturned call request)
      { s with abortPromise := some request, phase := .waitingAbort }) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem requestFinalize_eq :
  ∀ {α ε : Type} (s : State α ε) (reason : Boundary.Exception ε),
  requestFinalize s reason =
    emit s (.readyToFinalize reason) { s with phase := .readyToFinalize reason } := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem stepWritable_eq :
  ∀ {α ε : Type} (s : State α ε) (d : Option (Writable.Decision α ε)),
  stepWritable s d =
    (match d with
      | none => Writable.tick s.destination
      | some a => Writable.decide s.destination a).map
      (fun w => emit s (.writable d) { s with destination := w }) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem externalFrontier_eq :
  ∀ {α ε : Type} (s : State α ε),
  externalFrontier s = (match s.phase with
    | .readyToFinalize _ => false
    | _ => if Writable.externalFrontier s.destination then
        match s.destination.control with
        | [] => match s.phase with
            | .running | .waitingWrites | .waitingAbort => true
            | _ => false
        | _ => true
      else false) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem decide_eq :
  ∀ {α ε : Type} (s : State α ε) (d : Decision α ε),
  decide s d = (if externalFrontier s then match d with
    | .sourceError e => some (emit s (.sourceError e)
        { s with source := Readable.error s.source e })
    | .writable a => if foreignDecision a then stepWritable s (some a) else none
    else none) := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem tick_eq :
  ∀ {α ε : Type} (s : State α ε),
  tick s =
    let action := fun p : ShutdownPlan ε =>
      if p.preventAbort then some (requestFinalize s p.reason)
      else invokeAbort s p
    match s.phase with
    | .readyToFinalize _ => none
    | _ => if s.destination.control ≠ [] then stepWritable s none
      else match s.phase with
      | .running => match s.source.status with
          | .errored _ => some (enterForwardShutdown s)
          | .readable =>
              match s.destination.status with
              | .writable =>
                if Writable.closeQueuedOrInFlight s.destination then stepWritable s none
                else match Writable.desiredSize s.destination, nextUnwritten s.links with
                  | some size, some l =>
                      if Readable.sizePositive size then invokeWrite s l
                      else stepWritable s none
                  | _, _ => stepWritable s none
              | _ => stepWritable s none
          | .closed => stepWritable s none
      | .draining => match s.selection with
          | none => none
          | some p =>
              if p.drainRequired then match nextUnwritten s.links with
                | some l => invokeWrite s l
                | none => some (emit s .administrative { s with phase := .waitingWrites })
              else action p
      | .returningWrite id call => captureWrite s id call
      | .waitingWrites => match s.selection with
          | none => none
          | some p => if allWrittenSettled s.destination s.links then action p
              else stepWritable s none
      | .returningAbort call => captureAbort s call
      | .waitingAbort => match s.selection, s.abortPromise with
          | some p, some id => match Writable.lookupPromise s.destination id with
              | some (.fulfilled _) => some (requestFinalize s p.reason)
              | some (.rejected reason) => some (requestFinalize s reason)
              | _ => stepWritable s none
          | _, _ => none
      | .readyToFinalize _ => none := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem step_iff :
  ∀ {α ε : Type} (s t : State α ε) (d : Option (Decision α ε)),
  Step s d t ↔ (match d with | none => tick s | some a => decide s a) = some t := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem reaches_nil_iff :
  ∀ {α ε : Type} (s t : State α ε),
  Reaches s [] t ↔ s = t := by
  intro α ε s t
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst t
    exact Reaches.nil s

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem reaches_cons_iff :
  ∀ {α ε : Type} (s t : State α ε)
  (d : Option (Decision α ε)) (ds : List (Option (Decision α ε))),
  Reaches s (d :: ds) t ↔ ∃ mid, Step s d mid ∧ Reaches mid ds t := by
  intro α ε s t d ds
  constructor
  · intro h
    cases h with
    | cons step tail => exact ⟨_, step, tail⟩
  · rintro ⟨mid, step, tail⟩
    exact Reaches.cons step tail

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem reaches_append_iff :
  ∀ {α ε : Type} (s t : State α ε)
  (left right : List (Option (Decision α ε))),
  Reaches s (left ++ right) t ↔
    ∃ mid, Reaches s left mid ∧ Reaches mid right t := by
  intro α ε s t left
  induction left generalizing s with
  | nil =>
      intro right
      simp [reaches_nil_iff]
  | cons d ds ih =>
      intro right
      simp only [List.cons_append, reaches_cons_iff, ih]
      constructor
      · rintro ⟨first, hstep, mid, hleft, hright⟩
        exact ⟨mid, ⟨first, hstep, hleft⟩, hright⟩
      · rintro ⟨mid, ⟨first, hstep, hleft⟩, hright⟩
        exact ⟨first, hstep, mid, hleft, hright⟩

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem admitted_iff :
  ∀ {α ε : Type} (s : State α ε),
  Admitted s ↔ InitialSnapshot (snapshot s) ∧
    s.phase = .running ∧ s.entry = snapshot s ∧ s.trace = [] := by
  intros
  rfl

/-- Frozen local receipt under PIPING-PG-FORWARD-SHUTDOWN; no global mask claim. -/
theorem ready_frontier :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
  s.phase = .readyToFinalize e →
    tick s = none ∧ ∀ d, decide s d = none := by
  intro α ε s e h
  simp [tick, decide, externalFrontier, h]

private theorem deliveredReads_error {α ε : Type} (s : Readable.State α ε)
    (reason : Boundary.Exception ε) :
    deliveredReads (Readable.error s reason) = deliveredReads s := by
  cases h : s.status <;> simp [Readable.error, h, deliveredReads, List.filterMap_map]

private theorem markWrite_inventory {α : Type} (ls : List (ReadWriteLink α))
    (id : Nat) (stage : WriteStage) :
    (markWrite ls id stage).map (fun l => (l.readId, l.chunk)) =
      ls.map (fun l => (l.readId, l.chunk)) := by
  simp only [markWrite, List.map_map]
  apply List.map_congr_left
  intro l _
  dsimp only [Function.comp_apply]
  split <;> rfl

/-- Fields retained by every candidate transition, without an admission assumption. -/
private def Frame {α ε : Type} (s t : State α ε) : Prop :=
  t.source.nextRead = s.source.nextRead ∧
  deliveredReads t.source = deliveredReads s.source ∧
  t.links.map (fun l => (l.readId, l.chunk)) = s.links.map (fun l => (l.readId, l.chunk)) ∧
  t.preventAbort = s.preventAbort ∧
  ∀ p, s.selection = some p → t.selection = some p

private theorem frame_refl {α ε : Type} (s : State α ε) : Frame s s := by
  simp [Frame]

private theorem frame_stepWritable {α ε : Type} (s t : State α ε)
    (d : Option (Writable.Decision α ε)) (h : stepWritable s d = some t) : Frame s t := by
  simp only [stepWritable, Option.map_eq_some_iff] at h
  obtain ⟨w, _, rfl⟩ := h
  simp [Frame, emit]

private theorem frame_invokeWrite {α ε : Type} (s t : State α ε)
    (l : ReadWriteLink α) (h : invokeWrite s l = some t) : Frame s t := by
  simp only [invokeWrite, Option.map_eq_some_iff] at h
  obtain ⟨w, _, rfl⟩ := h
  simp [Frame, emit, markWrite_inventory]

private theorem frame_captureWrite {α ε : Type} (s t : State α ε)
    (id call : Nat) (h : captureWrite s id call = some t) : Frame s t := by
  simp only [captureWrite, Option.map_eq_some_iff] at h
  obtain ⟨request, _, rfl⟩ := h
  simp [Frame, emit, markWrite_inventory]

private theorem frame_invokeAbort {α ε : Type} (s t : State α ε)
    (p : ShutdownPlan ε) (h : invokeAbort s p = some t) : Frame s t := by
  simp only [invokeAbort, Option.map_eq_some_iff] at h
  obtain ⟨w, _, rfl⟩ := h
  simp [Frame, emit]

private theorem frame_captureAbort {α ε : Type} (s t : State α ε)
    (call : Nat) (h : captureAbort s call = some t) : Frame s t := by
  simp only [captureAbort, Option.map_eq_some_iff] at h
  obtain ⟨request, _, rfl⟩ := h
  simp [Frame, emit]

private theorem frame_finalize {α ε : Type} (s : State α ε) (reason : Boundary.Exception ε) :
    Frame s (requestFinalize s reason) := by
  simp [Frame, requestFinalize, emit]

private theorem frame_select {α ε : Type} (s : State α ε) :
    Frame s (enterForwardShutdown s) := by
  unfold enterForwardShutdown
  split <;> simp_all [Frame, emit]

private theorem frame_tick {α ε : Type} (s t : State α ε)
    (h : tick s = some t) : Frame s t := by
  unfold tick at h
  dsimp only at h
  repeat' first
    | exact frame_stepWritable s t _ h
    | exact frame_invokeWrite s t _ h
    | exact frame_captureWrite s t _ _ h
    | exact frame_invokeAbort s t _ h
    | exact frame_captureAbort s t _ h
    | cases h; exact frame_finalize s _
    | cases h; exact frame_select s
    | cases h; simp [Frame, emit]
    | contradiction
    | split at h

private theorem frame_decide {α ε : Type} (s t : State α ε)
    (d : Decision α ε) (h : decide s d = some t) : Frame s t := by
  unfold decide at h
  split at h
  · cases d with
    | sourceError reason =>
        cases h
        simp only [Frame, emit, deliveredReads_error]
        cases hs : s.source.status <;> simp [Readable.error, hs]
    | writable choice =>
        dsimp only at h
        split at h
        · exact frame_stepWritable s t _ h
        · contradiction
  · contradiction

private theorem frame_step {α ε : Type} (s t : State α ε)
    (d : Option (Decision α ε)) (h : Step s d t) : Frame s t := by
  cases d with
  | none => exact frame_tick s t h
  | some choice => exact frame_decide s t choice h

/-- No candidate run starts a new read, under the frozen shutdown-fragment observation. -/
theorem reaches_no_new_read :
  ∀ {α ε : Type} (s t : State α ε) (tape : List (Option (Decision α ε))),
  Admitted s → Reaches s tape t → t.source.nextRead = s.source.nextRead := by
  intro α ε s t tape admitted run
  clear admitted
  induction run with
  | nil => rfl
  | cons step _ ih => exact ih.trans (frame_step _ _ _ step).1

/-- Once selected, the exact shutdown plan survives every finite candidate run. -/
theorem reaches_selection_stable :
  ∀ {α ε : Type} (s t : State α ε) (tape : List (Option (Decision α ε)))
    (p : ShutdownPlan ε),
  s.selection = some p → Reaches s tape t → t.selection = some p := by
  intro α ε s t tape p selected run
  induction run with
  | nil => exact selected
  | cons step _ ih => exact ih ((frame_step _ _ _ step).2.2.2.2 p selected)

private def PromiseKeys {α ε : Type} (s : Writable.State α ε) : List Nat :=
  s.promises.map Prod.fst

/-- Only references that can produce a return event are needed for capture provenance. -/
private def ReturnRefs {α ε : Type} (s : Writable.State α ε) : Prop :=
  (∀ call id, Writable.Control.returnPromise call id ∈ s.control → id ∈ PromiseKeys s) ∧
  (∀ call id, Writable.Event.returned call id ∈ s.trace → id ∈ PromiseKeys s) ∧
  (match s.pendingAbort with
    | none => True
    | some (.requested id _) | some (.alreadyErroring id) => id ∈ PromiseKeys s)

private theorem promiseKeys_settle {α ε : Type} (s : Writable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    PromiseKeys (Writable.settle s id result) = PromiseKeys s := by
  unfold PromiseKeys Writable.settle
  dsimp only
  split
  · simp only [ite_true]
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_apply]
    split <;> simp_all
  · rfl

private theorem returned_settle {α ε : Type} (s : Writable.State α ε) (id call request : Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    Writable.Event.returned call request ∈ (Writable.settle s id result).trace ↔
      Writable.Event.returned call request ∈ s.trace := by
  unfold Writable.settle
  dsimp only
  split <;> simp

private theorem promiseKeys_fresh {α ε : Type} (s : Writable.State α ε)
    (outcome : Writable.UnitPromise ε) :
    PromiseKeys (Writable.freshPromise s outcome).1 = PromiseKeys s ++ [s.nextPromise] := by
  cases outcome <;> simp [Writable.freshPromise, PromiseKeys]

private theorem returned_fresh {α ε : Type} (s : Writable.State α ε) (call request : Nat)
    (outcome : Writable.UnitPromise ε) :
    Writable.Event.returned call request ∈ (Writable.freshPromise s outcome).1.trace ↔
      Writable.Event.returned call request ∈ s.trace := by
  cases outcome <;> simp [Writable.freshPromise]

private theorem refs_settle {α ε : Type} (s : Writable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) (h : ReturnRefs s) :
    ReturnRefs (Writable.settle s id result) := by
  simpa only [ReturnRefs, promiseKeys_settle, returned_settle,
    show (Writable.settle s id result).control = s.control from rfl,
    show (Writable.settle s id result).pendingAbort = s.pendingAbort from rfl] using h

private theorem refs_fresh {α ε : Type} (s : Writable.State α ε)
    (outcome : Writable.UnitPromise ε) (h : ReturnRefs s) :
    ReturnRefs (Writable.freshPromise s outcome).1 := by
  rcases h with ⟨hc, ht, ha⟩
  refine ⟨?_, ?_, ?_⟩
  · intro call id hm
    have hc' : (Writable.freshPromise s outcome).1.control = s.control := by
      cases outcome <;> rfl
    rw [hc'] at hm
    rw [promiseKeys_fresh]
    exact List.mem_append_left _ (hc call id hm)
  · intro call id hm
    rw [returned_fresh] at hm
    rw [promiseKeys_fresh]
    exact List.mem_append_left _ (ht call id hm)
  · have hp : (Writable.freshPromise s outcome).1.pendingAbort = s.pendingAbort := by
      cases outcome <;> rfl
    rw [hp]
    cases hab : s.pendingAbort with
    | none => trivial
    | some abort =>
        cases abort <;> simp only [hab] at ha ⊢ <;>
          rw [promiseKeys_fresh] <;> exact List.mem_append_left _ ha

private theorem fresh_control {α ε : Type} (s : Writable.State α ε)
    (outcome : Writable.UnitPromise ε) :
    (Writable.freshPromise s outcome).1.control = s.control := by
  cases outcome <;> rfl

private theorem fresh_pendingAbort {α ε : Type} (s : Writable.State α ε)
    (outcome : Writable.UnitPromise ε) :
    (Writable.freshPromise s outcome).1.pendingAbort = s.pendingAbort := by
  cases outcome <;> rfl

private theorem settle_control {α ε : Type} (s : Writable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    (Writable.settle s id result).control = s.control := rfl

private theorem settle_pendingAbort {α ε : Type} (s : Writable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    (Writable.settle s id result).pendingAbort = s.pendingAbort := rfl

private theorem fold_settle_projection {α ε β : Type} (f : Writable.State α ε → β)
    (result : Except (Boundary.Exception ε) Unit)
    (h : ∀ s id, f (Writable.settle s id result) = f s)
    (ids : List Nat) (s : Writable.State α ε) :
    f (ids.foldl (fun st id => Writable.settle st id result) s) = f s := by
  induction ids generalizing s with
  | nil => rfl
  | cons id ids ih => exact (ih _).trans (h s id)

private theorem fold_settle_keys {α ε : Type} (s : Writable.State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    PromiseKeys (ids.foldl (fun st id => Writable.settle st id result) s) = PromiseKeys s :=
  fold_settle_projection PromiseKeys result (fun _ _ => promiseKeys_settle _ _ _) ids s

private theorem fold_settle_control {α ε : Type} (s : Writable.State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    (ids.foldl (fun st id => Writable.settle st id result) s).control = s.control :=
  fold_settle_projection Writable.State.control result (fun _ _ => rfl) ids s

private theorem fold_settle_pendingAbort {α ε : Type} (s : Writable.State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    (ids.foldl (fun st id => Writable.settle st id result) s).pendingAbort = s.pendingAbort :=
  fold_settle_projection Writable.State.pendingAbort result (fun _ _ => rfl) ids s

private theorem returned_fold_settle {α ε : Type} (s : Writable.State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) Unit) (call request : Nat) :
    Writable.Event.returned call request ∈
        (ids.foldl (fun st id => Writable.settle st id result) s).trace ↔
      Writable.Event.returned call request ∈ s.trace := by
  induction ids generalizing s with
  | nil => rfl
  | cons id ids ih => exact (ih _).trans (returned_settle _ _ _ _ _)

private theorem refs_initial {α ε : Type} (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat) :
    ReturnRefs (Writable.initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed) := by
  simp [ReturnRefs, Writable.initial]

private theorem fresh_keys_map {α ε : Type} (s : Writable.State α ε)
    (outcome : Writable.UnitPromise ε) :
    (Writable.freshPromise s outcome).1.promises.map Prod.fst =
      s.promises.map Prod.fst ++ [s.nextPromise] := promiseKeys_fresh s outcome

private theorem fresh_id {α ε : Type} (s : Writable.State α ε)
    (outcome : Writable.UnitPromise ε) : (Writable.freshPromise s outcome).2 = s.nextPromise := rfl

private theorem settle_keys_map {α ε : Type} (s : Writable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    (Writable.settle s id result).promises.map Prod.fst = s.promises.map Prod.fst :=
  promiseKeys_settle s id result

private theorem fold_settle_keys_map {α ε : Type} (s : Writable.State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    (ids.foldl (fun st id => Writable.settle st id result) s).promises.map Prod.fst =
      s.promises.map Prod.fst := fold_settle_keys s ids result

private theorem refs_tick {α ε : Type} (s t : Writable.State α ε)
    (safe : ReturnRefs s) (step : Writable.tick s = some t) : ReturnRefs t := by
  unfold Writable.tick at step
  unfold Writable.invokeSink Writable.attachSink Writable.setOperationPhase
    Writable.clearAlgorithms Writable.ensureReadyRejected Writable.updateBackpressure
    Writable.markHandled at step
  dsimp only at step
  repeat' first
    | contradiction
    | split at step
    | cases step
  all_goals
    try simp only [ReturnRefs, PromiseKeys] at safe ⊢
    try simp only [settle_keys_map, returned_settle, fresh_keys_map, returned_fresh,
      fresh_control, fresh_pendingAbort, fresh_id, settle_control, settle_pendingAbort,
      fold_settle_keys_map, fold_settle_control, fold_settle_pendingAbort,
      returned_fold_settle] at *
    simp_all only [returned_fold_settle, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_true, and_true,
      Writable.Control.returnPromise.injEq, Writable.Event.returned.injEq] <;> grind

private theorem refs_decide {α ε : Type} (s t : Writable.State α ε)
    (d : Writable.Decision α ε) (safe : ReturnRefs s)
    (step : Writable.decide s d = some t) : ReturnRefs t := by
  unfold Writable.decide Writable.acceptAnswer Writable.attachSink
    Writable.setOperationPhase Writable.clearAlgorithms at step
  dsimp only at step
  repeat' first
    | contradiction
    | split at step
    | cases step
  all_goals simp_all [ReturnRefs, PromiseKeys] <;> grind

private theorem refs_step {α ε : Type} (s t : Writable.State α ε)
    (d : Option (Writable.Decision α ε)) (safe : ReturnRefs s)
    (step : Writable.Step s d t) : ReturnRefs t := by
  cases d with
  | none => exact refs_tick s t safe step
  | some choice => exact refs_decide s t choice safe step

private theorem lookup_of_keys {α ε : Type} (s : Writable.State α ε) (id : Nat)
    (h : id ∈ PromiseKeys s) : ∃ outcome, Writable.lookupPromise s id = some outcome := by
  apply Option.isSome_iff_exists.mp
  simpa [Writable.lookupPromise, PromiseKeys] using h

/-- Lift any invariant of canonical writable steps through the piping adapter. -/
private theorem destination_step {α ε : Type} (P : Writable.State α ε → Prop)
    (closed : ∀ w v d, P w → Writable.Step w d v → P v)
    (s t : State α ε) (d : Option (Decision α ε)) (hs : P s.destination)
    (step : Step s d t) : P t.destination := by
  have adapter : ∀ d, stepWritable s d = some t → P t.destination := by
    intro choice h
    simp only [stepWritable, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact closed _ _ choice hs hw
  have write : ∀ l, invokeWrite s l = some t → P t.destination := by
    intro l h
    simp only [invokeWrite, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact closed _ _ (some (.write l.chunk)) hs hw
  have abort : ∀ p, invokeAbort s p = some t → P t.destination := by
    intro p h
    simp only [invokeAbort, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact closed _ _ (some (.abort p.reason)) hs hw
  have captureWrite' : ∀ id call, captureWrite s id call = some t → P t.destination := by
    intro id call h
    simp only [captureWrite, Option.map_eq_some_iff] at h
    obtain ⟨request, _, rfl⟩ := h
    exact hs
  have captureAbort' : ∀ call, captureAbort s call = some t → P t.destination := by
    intro call h
    simp only [captureAbort, Option.map_eq_some_iff] at h
    obtain ⟨request, _, rfl⟩ := h
    exact hs
  unfold Step at step
  cases d with
  | none =>
      unfold tick at step
      dsimp only at step
      repeat' first
        | exact adapter _ step
        | exact write _ step
        | exact abort _ step
        | exact captureWrite' _ _ step
        | exact captureAbort' _ step
        | cases step; exact hs
        | cases step; unfold enterForwardShutdown; split <;> exact hs
        | contradiction
        | split at step
  | some choice =>
      unfold decide at step
      dsimp only at step
      repeat' first
        | exact adapter _ step
        | cases step; exact hs
        | contradiction
        | split at step

private theorem refs_reaches {α ε : Type} (s t : State α ε)
    (tape : List (Option (Decision α ε))) (hs : ReturnRefs s.destination)
    (run : Reaches s tape t) : ReturnRefs t.destination := by
  induction run with
  | nil => exact hs
  | cons step _ ih => exact ih (destination_step ReturnRefs refs_step _ _ _ hs step)

private theorem lookupReturn_event {α ε : Type} (s : Writable.State α ε) (call request : Nat)
    (h : lookupReturn s call = some request) : Writable.Event.returned call request ∈ s.trace := by
  obtain ⟨event, member, result⟩ := List.exists_of_findSome?_eq_some h
  clear h
  cases event <;> simp_all

private theorem capture_provenance {α ε : Type} (s : Writable.State α ε) (call request : Nat)
    (safe : ReturnRefs s) (h : lookupReturn s call = some request) :
    Writable.Event.returned call request ∈ s.trace ∧
      ∃ outcome, Writable.lookupPromise s request = some outcome := by
  have member := lookupReturn_event s call request h
  exact ⟨member, lookup_of_keys s request (safe.2.1 call request member)⟩

private def Prevention {α ε : Type} (s : State α ε) : Prop :=
  (∀ p, s.selection = some p → p.preventAbort = s.preventAbort) ∧
  (s.preventAbort = true → s.abortCall = none ∧ s.abortPromise = none ∧
    (∀ call, s.phase ≠ .returningAbort call) ∧ s.phase ≠ .waitingAbort ∧
    ∀ reason, s.phase = .readyToFinalize reason →
      ∃ p, s.selection = some p ∧ p.reason = reason)

private theorem prevention_admitted {α ε : Type} (s : State α ε) (h : Admitted s) :
    Prevention s := by
  rcases h with ⟨initial, phase, _, _⟩
  rcases initial with ⟨_, _, selection, abortCall, abortPromise, _⟩
  simp_all [Prevention, snapshot]

private theorem prevention_step {α ε : Type} (s t : State α ε)
    (d : Option (Decision α ε)) (safe : Prevention s) (step : Step s d t) : Prevention t := by
  unfold Step at step
  cases d <;> dsimp only at step
  all_goals first | unfold tick at step | unfold decide at step
  all_goals
    simp only [stepWritable, invokeWrite, captureWrite, invokeAbort, captureAbort,
      requestFinalize, enterForwardShutdown] at step
    repeat' first
      | contradiction
      | split at step
      | (simp only [Option.map_eq_some_iff] at step; obtain ⟨value, _, rfl⟩ := step)
      | cases step
    all_goals simp_all [Prevention, emit] <;> grind

/--
Under preventAbort, a finalization request retains the selected source reason and no abort IDs.
-/
theorem preventAbort_write_rejection_no_override :
  ∀ {α ε : Type} (s t : State α ε) (tape : List (Option (Decision α ε)))
    (reason : Boundary.Exception ε),
  Admitted s → s.preventAbort = true → Reaches s tape t →
    t.phase = .readyToFinalize reason →
      ∃ p, t.selection = some p ∧ p.reason = reason ∧
        t.abortCall = none ∧ t.abortPromise = none := by
  intro α ε s t tape reason admitted prevent run ready
  have invariant : Prevention t ∧ t.preventAbort = true := by
    have start := prevention_admitted s admitted
    clear admitted ready
    induction run with
    | nil => exact ⟨start, prevent⟩
    | cons step _ ih =>
        exact ih ((frame_step _ _ _ step).2.2.2.1.trans prevent)
          (prevention_step _ _ _ start step)
  obtain ⟨noCall, noPromise, _, _, final⟩ := invariant.1.2 invariant.2
  obtain ⟨p, selected, sameReason⟩ := final reason ready
  exact ⟨p, selected, sameReason, noCall, noPromise⟩

private theorem lookup_map_other {ε : Type} (ps : List (Nat × Writable.UnitPromise ε))
    (id target : Nat) (outcome : Writable.UnitPromise ε) (different : id ≠ target) :
    ((ps.map (fun p => if p.1 == target then (target, outcome) else p)).find?
      (fun p => p.1 == id)).map Prod.snd =
      (ps.find? (fun p => p.1 == id)).map Prod.snd := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨key, value⟩
      by_cases ht : key = target
      · subst key
        simpa [Ne.symm different] using ih
      · by_cases hi : key = id
        · simp [hi, different]
        · simpa [ht, hi] using ih

private theorem lookup_settle_other {α ε : Type} (s : Writable.State α ε)
    (id target : Nat) (result : Except (Boundary.Exception ε) Unit) (different : id ≠ target) :
    Writable.lookupPromise (Writable.settle s target result) id = Writable.lookupPromise s id := by
  unfold Writable.lookupPromise Writable.settle
  dsimp only
  split
  · simp only [ite_true]
    exact lookup_map_other s.promises id target _ different
  · rfl

private theorem lookup_settle_stable {α ε : Type} (s : Writable.State α ε)
    (id target : Nat) (result : Except (Boundary.Exception ε) Unit)
    (outcome : Writable.UnitPromise ε) (settled : outcome ≠ .pending)
    (found : Writable.lookupPromise s id = some outcome) :
    Writable.lookupPromise (Writable.settle s target result) id = some outcome := by
  by_cases same : id = target
  · subst target
    have unchanged : (Writable.settle s id result).promises = s.promises := by
      cases outcome <;> simp_all [Writable.settle]
    simpa only [Writable.lookupPromise, unchanged] using found
  · exact (lookup_settle_other s id target result same).trans found

private theorem lookup_fresh_stable {α ε : Type} (s : Writable.State α ε)
    (id : Nat) (before after : Writable.UnitPromise ε)
    (found : Writable.lookupPromise s id = some before) :
    Writable.lookupPromise (Writable.freshPromise s after).1 id = some before := by
  simp only [Writable.lookupPromise, Option.map_eq_some_iff] at found
  obtain ⟨pair, found, rfl⟩ := found
  cases after <;> simp [Writable.freshPromise, Writable.lookupPromise, List.find?_append, found]

private theorem lookup_fold_settle_stable {α ε : Type} (s : Writable.State α ε)
    (ids : List Nat) (id : Nat) (result : Except (Boundary.Exception ε) Unit)
    (outcome : Writable.UnitPromise ε) (settled : outcome ≠ .pending)
    (found : Writable.lookupPromise s id = some outcome) :
    Writable.lookupPromise (ids.foldl (fun st target => Writable.settle st target result) s) id =
      some outcome := by
  induction ids generalizing s with
  | nil => exact found
  | cons target ids ih => exact ih _ (lookup_settle_stable s id target result outcome settled found)

private theorem lookup_settle_unchanged {α ε : Type} (s : Writable.State α ε)
    (id target : Nat) (result : Except (Boundary.Exception ε) Unit)
    (settled : Writable.lookupPromise s id ≠ some .pending) :
    Writable.lookupPromise (Writable.settle s target result) id = Writable.lookupPromise s id := by
  by_cases same : id = target
  · subst target
    have unchanged : (Writable.settle s id result).promises = s.promises := by
      cases h : Writable.lookupPromise s id with
      | none => simp [Writable.settle, h]
      | some outcome => cases outcome <;> simp_all [Writable.settle]
    simp only [Writable.lookupPromise, unchanged]
  · exact lookup_settle_other s id target result same

private theorem lookup_fresh_unchanged {α ε : Type} (s : Writable.State α ε)
    (id : Nat) (after : Writable.UnitPromise ε)
    (present : (Writable.lookupPromise s id).isSome) :
    Writable.lookupPromise (Writable.freshPromise s after).1 id = Writable.lookupPromise s id := by
  obtain ⟨before, found⟩ := Option.isSome_iff_exists.mp present
  exact (lookup_fresh_stable s id before after found).trans found.symm

private theorem lookup_fold_settle_unchanged {α ε : Type} (s : Writable.State α ε)
    (ids : List Nat) (id : Nat) (result : Except (Boundary.Exception ε) Unit)
    (settled : Writable.lookupPromise s id ≠ some .pending) :
    Writable.lookupPromise (ids.foldl (fun st target => Writable.settle st target result) s) id =
      Writable.lookupPromise s id := by
  induction ids generalizing s with
  | nil => rfl
  | cons target ids ih =>
      have unchanged := lookup_settle_unchanged s id target result settled
      exact (ih _ (by rwa [unchanged])).trans unchanged

private theorem settle_query {α ε : Type} (s : Writable.State α ε)
    (id target : Nat) (result : Except (Boundary.Exception ε) Unit)
    (settled : (s.promises.find? (fun p => p.1 == id)).map Prod.snd ≠ some .pending) :
    ((Writable.settle s target result).promises.find? (fun p => p.1 == id)).map Prod.snd =
      (s.promises.find? (fun p => p.1 == id)).map Prod.snd :=
  lookup_settle_unchanged s id target result settled

private theorem fresh_query {α ε : Type} (s : Writable.State α ε)
    (id : Nat) (after : Writable.UnitPromise ε)
    (present : ((s.promises.find? (fun p => p.1 == id)).map Prod.snd).isSome) :
    ((Writable.freshPromise s after).1.promises.find? (fun p => p.1 == id)).map Prod.snd =
      (s.promises.find? (fun p => p.1 == id)).map Prod.snd :=
  lookup_fresh_unchanged s id after present

private theorem fold_settle_query {α ε : Type} (s : Writable.State α ε)
    (ids : List Nat) (id : Nat) (result : Except (Boundary.Exception ε) Unit)
    (settled : (s.promises.find? (fun p => p.1 == id)).map Prod.snd ≠ some .pending) :
    ((ids.foldl (fun st target => Writable.settle st target result) s).promises.find?
      (fun p => p.1 == id)).map Prod.snd =
      (s.promises.find? (fun p => p.1 == id)).map Prod.snd :=
  lookup_fold_settle_unchanged s ids id result settled

private theorem lookup_tick_stable {α ε : Type} (s t : Writable.State α ε)
    (id : Nat) (outcome : Writable.UnitPromise ε) (settled : outcome ≠ .pending)
    (found : Writable.lookupPromise s id = some outcome)
    (step : Writable.tick s = some t) : Writable.lookupPromise t id = some outcome := by
  unfold Writable.tick at step
  unfold Writable.invokeSink Writable.attachSink Writable.setOperationPhase
    Writable.clearAlgorithms Writable.ensureReadyRejected Writable.updateBackpressure
    Writable.markHandled at step
  dsimp only at step
  repeat' first
    | contradiction
    | split at step
    | cases step
  all_goals
    simp only [Writable.lookupPromise] at found ⊢
    simp_all (maxDischargeDepth := 4) only [settle_query, fresh_query, fold_settle_query,
      Option.some.injEq, ne_eq, not_false_eq_true, Option.isSome_some] <;> contradiction

private theorem lookup_decide_stable {α ε : Type} (s t : Writable.State α ε)
    (id : Nat) (outcome : Writable.UnitPromise ε) (d : Writable.Decision α ε)
    (found : Writable.lookupPromise s id = some outcome)
    (step : Writable.decide s d = some t) : Writable.lookupPromise t id = some outcome := by
  unfold Writable.decide Writable.acceptAnswer Writable.attachSink
    Writable.setOperationPhase Writable.clearAlgorithms at step
  dsimp only at step
  repeat' first
    | exact found
    | contradiction
    | split at step
    | cases step

private theorem lookup_step_stable {α ε : Type} (s t : Writable.State α ε)
    (id : Nat) (outcome : Writable.UnitPromise ε) (d : Option (Writable.Decision α ε))
    (settled : outcome ≠ .pending) (found : Writable.lookupPromise s id = some outcome)
    (step : Writable.Step s d t) : Writable.lookupPromise t id = some outcome := by
  cases d with
  | none => exact lookup_tick_stable s t id outcome settled found step
  | some choice => exact lookup_decide_stable s t id outcome choice found step

private theorem lookup_piping_step_stable {α ε : Type} (s t : State α ε)
    (id : Nat) (outcome : Writable.UnitPromise ε) (d : Option (Decision α ε))
    (settled : outcome ≠ .pending) (found : Writable.lookupPromise s.destination id = some outcome)
    (step : Step s d t) : Writable.lookupPromise t.destination id = some outcome :=
  destination_step (fun w => Writable.lookupPromise w id = some outcome)
    (fun w v choice h => lookup_step_stable w v id outcome choice settled h) s t d found step

private theorem frame_inventory {α ε : Type} (s t : State α ε) (h : Frame s t)
    (inventory : ReadInventory (snapshot s)) : ReadInventory (snapshot t) := by
  have keys : t.links.map ReadWriteLink.readId = s.links.map ReadWriteLink.readId := by
    have pairs := congrArg (List.map Prod.fst) h.2.2.1
    simpa only [List.map_map, Function.comp_def] using pairs
  exact ⟨h.2.2.1.trans (inventory.1.trans h.2.1.symm), keys ▸ inventory.2⟩

/--
Candidate phases justify the references and captured drain required by the independent records.
-/
private def ProtocolShape {α ε : Type} (s : State α ε) : Prop :=
  match s.phase with
  | .running => s.selection = none ∧ s.abortCall = none ∧ s.abortPromise = none
  | .draining | .waitingWrites =>
      (∃ p, s.selection = some p) ∧ s.abortCall = none ∧ s.abortPromise = none
  | .returningWrite id call =>
      s.abortCall = none ∧ s.abortPromise = none ∧
      ∃ l ∈ s.links, l.readId = id ∧ l.write = .invoking call
  | .returningAbort call =>
      ∃ p, s.selection = some p ∧ p.preventAbort = false ∧
        s.abortCall = some call ∧ s.abortPromise = none ∧
        (p.drainRequired = false ∨ WritesSettled (snapshot s))
  | .waitingAbort =>
      ∃ p call request, s.selection = some p ∧ p.preventAbort = false ∧
        s.abortCall = some call ∧ s.abortPromise = some request ∧
        (p.drainRequired = false ∨ WritesSettled (snapshot s))
  | .readyToFinalize _ => True

private theorem shape_admitted {α ε : Type} (s : State α ε) (h : Admitted s) :
    ProtocolShape s := by
  rcases h with ⟨initial, phase, _, _⟩
  rcases initial with ⟨_, _, selection, abortCall, abortPromise, _⟩
  simp_all [ProtocolShape, snapshot]

private theorem nextUnwritten_spec {α : Type} (ls : List (ReadWriteLink α))
    (l : ReadWriteLink α) (h : nextUnwritten ls = some l) :
    ∃ pre post, ls = pre ++ l :: post ∧
      (∀ earlier ∈ pre, earlier.write ≠ .unwritten) ∧ l.write = .unwritten := by
  induction ls with
  | nil => simp [nextUnwritten] at h
  | cons head tail ih =>
      cases hw : head.write with
      | unwritten =>
          simp only [nextUnwritten, hw, Option.some.injEq] at h
          subst l
          exact ⟨[], tail, rfl, by simp, hw⟩
      | invoking call =>
          have ht : nextUnwritten tail = some l := by simpa only [nextUnwritten, hw] using h
          obtain ⟨pre, post, rest, earlier, write⟩ := ih ht
          refine ⟨head :: pre, post, by simp [rest], ?_, write⟩
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · simp [hw]
          · exact earlier other member
      | submitted call request =>
          have ht : nextUnwritten tail = some l := by simpa only [nextUnwritten, hw] using h
          obtain ⟨pre, post, rest, earlier, write⟩ := ih ht
          refine ⟨head :: pre, post, by simp [rest], ?_, write⟩
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · simp [hw]
          · exact earlier other member

private theorem nextUnwritten_member {α : Type} (ls : List (ReadWriteLink α))
    (l : ReadWriteLink α) (h : nextUnwritten ls = some l) : l ∈ ls := by
  obtain ⟨pre, post, rfl, _, _⟩ := nextUnwritten_spec ls l h
  simp

private theorem markWrite_member {α : Type} (ls : List (ReadWriteLink α))
    (l : ReadWriteLink α) (stage : WriteStage) (member : l ∈ ls) :
    ∃ next ∈ markWrite ls l.readId stage, next.readId = l.readId ∧ next.write = stage := by
  refine ⟨{ l with write := stage }, ?_, rfl, rfl⟩
  exact List.mem_map.mpr ⟨l, member, by simp⟩

private theorem writesSettled_destination {α ε : Type} (s : Snapshot α ε)
    (w : Writable.State α ε) (d : Option (Writable.Decision α ε))
    (step : Writable.Step s.destination d w) (settled : WritesSettled s) :
    WritesSettled { s with destination := w } := by
  intro l member
  obtain ⟨call, request, write, outcome⟩ := settled l member
  refine ⟨call, request, write, ?_⟩
  rcases outcome with fulfilled | ⟨reason, rejected⟩
  · exact Or.inl (lookup_step_stable s.destination w request (.fulfilled ()) d
      (by simp) fulfilled step)
  · exact Or.inr ⟨reason, lookup_step_stable s.destination w request (.rejected reason) d
      (by simp) rejected step⟩

private theorem shape_stepWritable {α ε : Type} (s t : State α ε)
    (d : Option (Writable.Decision α ε)) (safe : ProtocolShape s)
    (step : stepWritable s d = some t) : ProtocolShape t := by
  simp only [stepWritable, Option.map_eq_some_iff] at step
  obtain ⟨w, hw, rfl⟩ := step
  have drain := writesSettled_destination (snapshot s) w d hw
  cases hp : s.phase <;> simp_all [ProtocolShape, emit, snapshot] <;> grind

private theorem shape_invokeWrite {α ε : Type} (s t : State α ε) (l : ReadWriteLink α)
    (safe : ProtocolShape s) (phase : s.phase = .running ∨ s.phase = .draining)
    (next : nextUnwritten s.links = some l) (step : invokeWrite s l = some t) :
    ProtocolShape t := by
  simp only [invokeWrite, Option.map_eq_some_iff] at step
  obtain ⟨w, _, rfl⟩ := step
  have member := markWrite_member s.links l (.invoking s.destination.nextCall)
    (nextUnwritten_member s.links l next)
  rcases phase with phase | phase <;> simp_all [ProtocolShape, emit]

private theorem shape_captureWrite {α ε : Type} (s t : State α ε) (id call : Nat)
    (safe : ProtocolShape s) (phase : s.phase = .returningWrite id call)
    (step : captureWrite s id call = some t) : ProtocolShape t := by
  simp only [captureWrite, Option.map_eq_some_iff] at step
  obtain ⟨request, _, rfl⟩ := step
  cases selected : s.selection <;> simp_all [ProtocolShape, emit]

private theorem shape_invokeAbort {α ε : Type} (s t : State α ε) (p : ShutdownPlan ε)
    (selected : s.selection = some p) (prevent : p.preventAbort = false)
    (noPromise : s.abortPromise = none)
    (drain : p.drainRequired = false ∨ WritesSettled (snapshot s))
    (step : invokeAbort s p = some t) : ProtocolShape t := by
  simp only [invokeAbort, Option.map_eq_some_iff] at step
  obtain ⟨w, hw, rfl⟩ := step
  refine ⟨p, selected, prevent, rfl, noPromise, ?_⟩
  rcases drain with skip | drained
  · exact Or.inl skip
  · exact Or.inr (writesSettled_destination (snapshot s) w (some (.abort p.reason)) hw drained)

private theorem shape_captureAbort {α ε : Type} (s t : State α ε) (call : Nat)
    (safe : ProtocolShape s) (phase : s.phase = .returningAbort call)
    (step : captureAbort s call = some t) : ProtocolShape t := by
  simp only [captureAbort, Option.map_eq_some_iff] at step
  obtain ⟨request, _, rfl⟩ := step
  simp only [ProtocolShape, phase] at safe
  obtain ⟨p, selected, prevent, abortCall, _, drain⟩ := safe
  exact ⟨p, call, request, selected, prevent, abortCall, rfl, drain⟩

private theorem shape_select {α ε : Type} (s : State α ε) (safe : ProtocolShape s)
    (phase : s.phase = .running) : ProtocolShape (enterForwardShutdown s) := by
  unfold enterForwardShutdown
  split <;> simp_all [ProtocolShape, emit]

private theorem shape_tick {α ε : Type} (s t : State α ε)
    (safe : ProtocolShape s) (step : tick s = some t) : ProtocolShape t := by
  have wait := allWrittenSettled_iff (snapshot s)
  change (allWrittenSettled s.destination s.links = true ↔ WritesSettled (snapshot s)) at wait
  unfold tick at step
  dsimp only at step
  repeat' first
    | exact shape_stepWritable s t _ safe step
    | exact shape_invokeWrite s t _ safe (by simp_all) (by assumption) step
    | exact shape_captureWrite s t _ _ safe (by assumption) step
    | exact shape_captureAbort s t _ safe (by assumption) step
    | exact shape_invokeAbort s t _ (by assumption) (by simp_all)
        (by simp_all [ProtocolShape]) (by simp_all) step
    | cases step; exact shape_select s safe (by assumption)
    | cases step; simp_all [ProtocolShape, requestFinalize, emit]
    | contradiction
    | split at step

private theorem shape_decide {α ε : Type} (s t : State α ε) (d : Decision α ε)
    (safe : ProtocolShape s) (step : decide s d = some t) : ProtocolShape t := by
  unfold decide at step
  repeat' first
    | exact shape_stepWritable s t _ safe step
    | cases step; exact safe
    | contradiction
    | split at step

private theorem shape_step {α ε : Type} (s t : State α ε) (d : Option (Decision α ε))
    (safe : ProtocolShape s) (step : Step s d t) : ProtocolShape t := by
  cases d with
  | none => exact shape_tick s t safe step
  | some choice => exact shape_decide s t choice safe step

private structure Invariant {α ε : Type} (s : State α ε) : Prop where
  inventory : ReadInventory (snapshot s)
  references : ReturnRefs s.destination
  shape : ProtocolShape s

private theorem invariant_admitted {α ε : Type} (s : State α ε) (h : Admitted s) : Invariant s := by
  refine ⟨h.1.1, ?_, shape_admitted s h⟩
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hwm, alg, seed, destination⟩
  change s.destination = Writable.initial hwm alg seed s.source.nextError at destination
  rw [destination]
  exact refs_initial _ _ _ _

private theorem invariant_step {α ε : Type} (s t : State α ε) (d : Option (Decision α ε))
    (safe : Invariant s) (step : Step s d t) : Invariant t :=
  ⟨frame_inventory s t (frame_step s t d step) safe.inventory,
    destination_step ReturnRefs refs_step s t d safe.references step,
    shape_step s t d safe.shape step⟩

private theorem step_nonfinal {α ε : Type} (s t : State α ε) (d : Option (Decision α ε))
    (step : Step s d t) : (snapshot s).finalization = none := by
  cases hp : s.phase <;> simp only [snapshot, hp]
  have stopped := ready_frontier s _ hp
  cases d with
  | none => simp only [Step, stopped.1] at step; cases step
  | some choice => simp only [Step, stopped.2 choice] at step; cases step

private def Emits {α ε : Type} (s t : State α ε) : Prop :=
  ∃ event, t.entry = s.entry ∧
    t.trace = s.trace ++ [⟨snapshot s, event, snapshot t⟩] ∧
    RecordAllowed ⟨snapshot s, event, snapshot t⟩

private theorem step_emits {α ε : Type} (s t : State α ε) (d : Option (Decision α ε))
    (safe : Invariant s) (step : Step s d t) : Emits s t := by
  have frame := frame_step s t d step
  have inventory := frame_inventory s t frame safe.inventory
  have nonfinal := step_nonfinal s t d step
  have shape := safe.shape
  have noClose : Writable.closeQueuedOrInFlight s.destination = false ↔
      s.destination.closeState = .none := by
    cases hc : s.destination.closeState <;> simp [Writable.closeQueuedOrInFlight, hc]
  have wait := allWrittenSettled_iff (snapshot s)
  change (allWrittenSettled s.destination s.links = true ↔ WritesSettled (snapshot s)) at wait
  unfold Step at step
  cases d <;> dsimp only at step
  all_goals first | unfold tick at step | unfold decide at step
  all_goals
    simp only [stepWritable, invokeWrite, captureWrite, invokeAbort, captureAbort,
      requestFinalize, enterForwardShutdown] at step
    repeat' first
      | contradiction
      | split at step
      | (simp only [Option.map_eq_some_iff] at step; obtain ⟨value, result, rfl⟩ := step)
      | cases step
    all_goals
      try have next := nextUnwritten_spec s.links _ (by assumption)
      try have returned := capture_provenance s.destination _ _ safe.references (by assumption)
      try simp_all only [ProtocolShape]
      try contradiction
      first
      | refine ⟨_, rfl, rfl, nonfinal, safe.inventory, inventory, frame.2.2.2.1, frame.1, ?_⟩
        simp_all [snapshot, emit, Writable.Step, foreignDecision_iff, drainGuard_true_iff] <;> grind
      | exfalso; grind

private theorem chain_append {α ε : Type} (a b c : Snapshot α ε)
    (left right : List (ProtocolRecord α ε))
    (first : ObservationChain a left b) (second : ObservationChain b right c) :
    ObservationChain a (left ++ right) c := by
  induction left generalizing a with
  | nil => cases first; exact second
  | cons record rest ih => exact ⟨first.1, ih record.after first.2⟩

private theorem specification_extend {α ε : Type} (s t : State α ε)
    (specification : ForwardShutdownSpec (observeShutdown s)) (emits : Emits s t) :
    ForwardShutdownSpec (observeShutdown t) := by
  obtain ⟨initial, chain, allowed⟩ := specification
  obtain ⟨event, entry, trace, rule⟩ := emits
  refine ⟨?_, ?_, ?_⟩
  · change InitialSnapshot t.entry
    rwa [entry]
  · change ObservationChain t.entry t.trace (snapshot t)
    rw [entry, trace]
    exact chain_append s.entry (snapshot s) (snapshot t) s.trace _ chain ⟨rfl, rfl⟩
  · intro record member
    change record ∈ t.trace at member
    rw [trace] at member
    rcases List.mem_append.mp member with old | last
    · exact allowed record old
    · simpa only [List.mem_singleton.mp last] using rule

private theorem specification_reaches {α ε : Type} (s t : State α ε)
    (tape : List (Option (Decision α ε))) (run : Reaches s tape t) :
    Invariant s → ForwardShutdownSpec (observeShutdown s) →
      ForwardShutdownSpec (observeShutdown t) := by
  induction run with
  | nil => intro _ specification; exact specification
  | cons step _ ih =>
      intro safe specification
      exact ih (invariant_step _ _ _ safe step)
        (specification_extend _ _ specification (step_emits _ _ _ safe step))

/-- Every admitted finite candidate run realizes the independent forward-shutdown fragment. -/
theorem forwardShutdown_realizes :
  ∀ {α ε : Type} (s t : State α ε) (tape : List (Option (Decision α ε))),
  Admitted s → Reaches s tape t → ForwardShutdownSpec (observeShutdown t) := by
  intro α ε s t tape admitted run
  apply specification_reaches s t tape run (invariant_admitted s admitted)
  obtain ⟨initial, _, entry, trace⟩ := admitted
  simpa only [ForwardShutdownSpec, observeShutdown, entry, trace, ObservationChain,
    List.not_mem_nil, false_implies, implies_true, and_true] using initial

end Whatwg.Streams.Piping
