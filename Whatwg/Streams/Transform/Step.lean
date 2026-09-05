import Whatwg.Streams.Transform.DefaultController

/-!
# Coupled transform transitions

TRANSFORM-PG-BACKPRESSURE owns this finite local integration order. Component
jobs execute through P4/P5; native ports are never foreign-answer decisions.
Global promise/adoption order and reachable-state invariants remain open.
-/

namespace Whatwg.Streams.Transform

/-- Run a coupled job through its canonical component, checking the retained writable request. -/
def runJob {α β ε : Type} (s : State α β ε) (job : Job α ε) : Option (State α β ε) :=
  match job with
  | .reaction reaction answer => react s reaction answer
  | .readable _ => do
      let r ← Readable.runPullJob s.readable
      servicePull (withReadable s r)
  | .writable request =>
      match s.writable.control, s.writable.jobs with
      | [], first :: _ =>
          if first.kind = .write ∧ first.request = request then
            (Writable.tick s.writable).map (withWritable s)
          else none
      | _, _ => none

/-- One deterministic synchronous continuation, native port service, or oldest coupled job. -/
def tick {α β ε : Type} (s : State α β ε) : Option (State α β ε) :=
  match s.control with
  | .errorWritable e :: tail =>
      let t := withWritable s
        { s.writable with control := .errorIfNeeded e :: s.writable.control }
      some { t with control := .waitWritable s.writable.control.length :: tail }
  | .waitWritable depth :: tail =>
      if s.writable.control.length = depth then some { s with control := tail }
      else if depth < s.writable.control.length then
        (Writable.tick s.writable).map (withWritable s)
      else none
  | .unblock :: tail => unblockWrite { s with control := tail }
  | .settle result answer :: tail => settle { s with control := tail } result answer
  | .awaitTransform _ _ depth :: _ =>
      if depth < s.writable.control.length then
        (Writable.tick s.writable).map (withWritable s)
      else none
  | [] =>
      match s.writable.control with
      | [] =>
          if s.readable.frames.isEmpty then
            match s.jobs with
            | job :: tail => runJob { s with jobs := tail } job
            | [] => none
          else servicePull s
      | .awaitSink (.write _ _) :: _ => sinkWrite s
      | _ =>
          if Writable.externalFrontier s.writable then none
          else (Writable.tick s.writable).map (withWritable s)

/-- Actual external boundaries: ordinary consumer calls and live foreign bodies, never ports. -/
def externalFrontier {α β ε : Type} (s : State α β ε) : Bool :=
  if s.readable.frames.isEmpty then
    match s.control with
    | [] =>
        match s.writable.control with
        | .awaitSink _ :: _ => false
        | _ => Writable.externalFrontier s.writable
    | .awaitTransform _ _ depth :: _ =>
        Decidable.decide (depth ≤ s.writable.control.length) &&
          Writable.externalFrontier s.writable
    | _ => false
  else false

/-- The frozen count-profile external decisions; callback returns and later answers are distinct. -/
inductive Decision (α β ε : Type) where
  | read
  | write (chunk : α)
  | enqueue (chunk : β)
  | error (reason : Boundary.Exception ε)
  | terminate
  | desiredSize
  | ready
  | closed
  | writerDesiredSize
  | returnSize (answer : Data.SizeAnswer Data.DyadicSize (Boundary.Exception ε))
  | returnTransform (result : Readable.PullReturn ε)
  | answerTransform (request : Nat) (answer : Readable.PullAnswer ε)

/-- Dispatch each admitted external decision to its canonical component or transform algorithm. -/
def decide {α β ε : Type} (s : State α β ε) (decision : Decision α β ε) :
    Option (State α β ε) :=
  if externalFrontier s then
    match decision with
    | .read => read s
    | .enqueue chunk => enqueue s chunk
    | .error reason => some (error s reason)
    | .terminate => some (terminate s)
    | .write chunk => (Writable.decide s.writable (.write chunk)).map (withWritable s)
    | .returnSize a => (Writable.decide s.writable (.returnSize a)).map (withWritable s)
    | .ready => (Writable.decide s.writable .queryReady).map (withWritable s)
    | .closed => (Writable.decide s.writable .queryClosed).map (withWritable s)
    | .writerDesiredSize =>
        (Writable.decide s.writable .queryDesiredSize).map (withWritable s)
    | .desiredSize => some (withReadable s (Readable.queryDesiredSize s.readable))
    | .returnTransform ret => returnTransform s ret
    | .answerTransform request answer => answerTransform s request answer
  else none

/-- The graph of an actual coupled external decision or deterministic internal tick. -/
def Step {α β ε : Type} (s : State α β ε) (decision : Option (Decision α β ε))
    (t : State α β ε) : Prop :=
  (match decision with | none => tick s | some d => decide s d) = some t

/-- Finite local derivations, including internal steps, without fuel as a semantic parameter. -/
inductive Reaches {α β ε : Type} :
    State α β ε → List (Option (Decision α β ε)) → State α β ε → Prop
  | nil (s : State α β ε) : Reaches s [] s
  | cons {s middle last : State α β ε} {d : Option (Decision α β ε)}
      {ds : List (Option (Decision α β ε))} :
      Step s d middle → Reaches middle ds last → Reaches s (d :: ds) last

end Whatwg.Streams.Transform
