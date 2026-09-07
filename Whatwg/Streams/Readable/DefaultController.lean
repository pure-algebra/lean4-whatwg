import Whatwg.Streams.Readable.State

/-!
# Readable.DefaultController.lean

Owner: the `ReadableStreamDefaultController` state and its abstract
operations: enqueue, close, error, the pull-again bookkeeping, and the
desired size it reports.

Spec anchors: `rs-default-controller-class`,
`rs-default-controller-internal-slots`,
`rs-default-controller-abstract-ops`.

Opens in P4.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
The P2 description above records this module's origin. The implementation below
is now admitted by the frozen P4a packet and `READABLE-PG-DEFAULT`. Its functions
operate on the post-start default-reader view; they are not the public IDL wrappers.
Slot and transition equations contribute to the local M1/M2 observations.
-/

namespace Whatwg.Streams.Readable

variable {α ε : Type}

/-- `op.readable-stream-default-controller-get-desired-size`, in the P3 exact numeric view. -/
def desiredSize (s : State α ε) : Option Size :=
  match s.status with
  | .errored _ => none
  | .closed => some sizes.zero
  | .readable => some (sizes.sub s.highWaterMark s.queue.totalSize)

/-- `op.readable-stream-default-controller-can-close-or-enqueue`: the entry guard. -/
def canCloseOrEnqueue (s : State α ε) : Bool :=
  match s.status with
  | .readable => !s.closeRequested
  | _ => false

/-- `op.readable-stream-default-controller-should-call-pull`, with the default reader attached. -/
def shouldCallPull (s : State α ε) : Bool :=
  canCloseOrEnqueue s && s.started &&
    (!s.readRequests.isEmpty || sizePositive (sizes.sub s.highWaterMark s.queue.totalSize))

/-- `op.rs-default-controller-private-pull` and enqueue: resume the saved post-pull work. -/
def continuePull (s : State α ε) : PullContinuation α → State α ε
  | .done => s
  | .settleRead id chunk =>
      { s with
        readPromises := s.readPromises.map fun p =>
          if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p
        trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
  | .returnEnqueue call =>
      { s with trace := s.trace ++ [.enqueueReturned call (.ok ())] }

/-- `op.readable-stream-default-controller-call-pull-if-needed`, suspending at invocation. -/
def callPullIfNeededWith (s : State α ε) (k : PullContinuation α) : State α ε :=
  if shouldCallPull s then
    if s.pulling then continuePull { s with pullAgain := true } k
    else match s.algorithms with
      | none => continuePull s k
      | some a =>
          { s with
            pulling := true, pullAwaiting := false, frames := .pull k :: s.frames,
            trace := s.trace ++ [.pullCalled a.pull] }
  else continuePull s k

/-- The call-pull algorithm when no enclosing read or enqueue remains to finish. -/
def callPullIfNeeded (s : State α ε) : State α ε := callPullIfNeededWith s .done

/-- `op.readable-stream-close`, expanded for the attached default reader. -/
def streamClose (s : State α ε) : State α ε :=
  match s.status with
  | .readable =>
      { s with
        status := .closed, readRequests := [], closedPromise := .fulfilled (),
        readPromises := s.readPromises.map fun p =>
          if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p
        trace := s.trace ++ [.settled (.closed (.ok ()))] ++
          s.readRequests.map (fun id => .settled (.read id (.ok .done))) }
  | _ => s

/-- `op.readable-stream-default-controller-close`: defer closure while queued chunks remain. -/
def close (s : State α ε) : State α ε :=
  if canCloseOrEnqueue s then
    let t := { s with closeRequested := true }
    if s.queue.entries = [] then streamClose { t with algorithms := none } else t
  else s

/-- `op.readable-stream-default-controller-error` followed by `op.readable-stream-error`. -/
def error (s : State α ε) (e : Boundary.Exception ε) : State α ε :=
  match s.status with
  | .readable =>
      { s with
        status := .errored e, queue := Data.resetQueue sizes s.queue,
        algorithms := none, readRequests := [], closedPromise := .rejected e,
        readPromises := s.readPromises.map fun p =>
          if p.1 ∈ s.readRequests then (p.1, .rejected e) else p
        trace := s.trace ++ [.settled (.closed (.error e))] ++
          s.readRequests.map (fun id => .settled (.read id (.error e))) }
  | _ => s

/-- Match the synchronous pull return, attach its reaction, then finish the enclosing operation. -/
def returnPull (s : State α ε) (result : PullReturn ε) : Option (State α ε) :=
  match s.frames with
  | .pull k :: rest =>
      let t := match result with
        | .pending => { s with frames := rest, pullAwaiting := true }
        | .settled answer =>
            { s with frames := rest, pullAwaiting := false, jobs := s.jobs ++ [answer] }
      some (continuePull t k)
  | _ => none

/-- Admit an eventual pull settlement only after its pending promise was returned. -/
def acceptPullAnswer (s : State α ε) (answer : PullAnswer ε) : Option (State α ε) :=
  if s.pullAwaiting then some { s with pullAwaiting := false, jobs := s.jobs ++ [answer] }
  else none

/-- The two registered reactions in `op.readable-stream-default-controller-call-pull-if-needed`. -/
def reactPull (s : State α ε) : PullAnswer ε → State α ε
  | .fulfilled =>
      if s.pullAgain then callPullIfNeeded { s with pulling := false, pullAgain := false }
      else { s with pulling := false }
  | .rejected e => error s e

/-- Run the oldest queued reaction only outside a synchronous callback stack. -/
def runPullJob (s : State α ε) : Option (State α ε) :=
  if s.frames = [] then
    match s.jobs with
    | [] => none
    | answer :: rest => some (reactPull { s with jobs := rest } answer)
  else none

/-- Resume `op.readable-stream-default-controller-enqueue` after sizing, without a second guard. -/
def finishEnqueue (s : State α ε) (call : Nat) (chunk : α) :
    Data.SizeAnswer Size (Boundary.Exception ε) → State α ε
  | .thrown e =>
      let t := error s e
      { t with trace := t.trace ++ [.enqueueReturned call (.error e)] }
  | .value size =>
      match Data.enqueueValueWithSize sizes s.queue chunk size with
      | .ok q => callPullIfNeededWith { s with queue := q } (.returnEnqueue call)
      | .error e =>
          let reason : Boundary.Exception ε := Boundary.Exception.ofRangeError s.nextError e
          let t := error { s with nextError := s.nextError + 1 } reason
          { t with trace := t.trace ++ [.enqueueReturned call (.error reason)] }

/-- Enter `op.readable-stream-default-controller-enqueue`; a pending read bypasses size. -/
def beginEnqueue (s : State α ε) (chunk : α) : State α ε :=
  if canCloseOrEnqueue s then
    match s.readRequests with
    | id :: rest =>
        callPullIfNeededWith
          { s with
            readRequests := rest, nextEnqueue := s.nextEnqueue + 1,
            readPromises := s.readPromises.map fun p =>
              if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p
            trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
          (.returnEnqueue s.nextEnqueue)
    | [] =>
        match s.algorithms with
        | none => s
        | some a =>
            match a.size with
            | .one =>
                finishEnqueue { s with nextEnqueue := s.nextEnqueue + 1 }
                  s.nextEnqueue chunk (.value sizes.one)
            | .foreign name =>
                { s with
                  nextEnqueue := s.nextEnqueue + 1,
                  frames := .size s.nextEnqueue chunk :: s.frames,
                  trace := s.trace ++ [.sizeCalled s.nextEnqueue name chunk] }
  else s

/-- Match the innermost suspended size call; an unmatched answer has no transition. -/
def resumeSize (s : State α ε) (answer : Data.SizeAnswer Size (Boundary.Exception ε)) :
    Option (State α ε) :=
  match s.frames with
  | .size call chunk :: rest => some (finishEnqueue { s with frames := rest } call chunk answer)
  | _ => none

/-- Record the consumer's desiredSize query for the local M2 view. -/
def queryDesiredSize (s : State α ε) : State α ε :=
  { s with trace := s.trace ++ [.desiredSizeRead (desiredSize s)] }

end Whatwg.Streams.Readable
