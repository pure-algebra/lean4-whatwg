import Whatwg.Streams.Readable.DefaultController

/-!
# Readable.DefaultReader.lean

Owner: the `ReadableStreamDefaultReader` state, its read requests as an
ordered list of pending answers, and the reader abstract operations that
fulfil or reject them.

Spec anchors: `default-reader-class`, `default-reader-internal-slots`,
`rs-reader-abstract-ops`.

Opens in P4.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-! The frozen P4a packet now supplies the post-start, fixed-reader implementation below. -/

namespace Whatwg.Streams.Readable

/-- `op.readable-stream-default-reader-read` and `op.rs-default-controller-private-pull`.
The already-dequeued chunk is saved across synchronous pull reentrancy, under local M1/M2. -/
def read {α ε : Type} (s : State α ε) : State α ε :=
  match s.status with
  | .closed =>
      let (t, id) := freshReadCell s (.fulfilled .done)
      { t with trace := t.trace ++ [.settled (.read id (.ok .done))] }
  | .errored e =>
      let (t, id) := freshReadCell s (.rejected e)
      { t with trace := t.trace ++ [.settled (.read id (.error e))] }
  | .readable =>
      match Data.dequeueValue sizes s.queue with
      | none =>
          let (t, id) := freshReadCell s .pending
          callPullIfNeeded { t with readRequests := t.readRequests ++ [id] }
      | some (chunk, q) =>
          let (t, id) := freshReadCell { s with queue := q } .pending
          if s.closeRequested = true ∧ q.entries = [] then
            continuePull (streamClose { t with algorithms := none }) (.settleRead id chunk)
          else callPullIfNeededWith t (.settleRead id chunk)

end Whatwg.Streams.Readable
