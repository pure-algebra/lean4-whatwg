import Whatwg.Streams

/-!
Retained P7a finite discriminators; freeze state and receipts: owning contract.
These compare named competing decisions at prescribed canonical snapshots.
They are not whole host or lifecycle executions. The quantified canonical
Reaches obligations and independent requirements bridge own those claims.
-/

set_option autoImplicit false
open Whatwg.Streams

namespace WhatwgTest.Streams.Counterexamples.Piping

private def settled : Writable.UnitPromise Nat → Bool
  | .pending => false
  | .fulfilled _ | .rejected _ => true

private def fulfilled : Writable.UnitPromise Nat → Bool
  | .fulfilled _ => true
  | _ => false

private def allSettled (cells : List (Writable.UnitPromise Nat)) : Bool := cells.all settled

private def finishReason (original : Boundary.Exception Nat) :
    Writable.UnitPromise Nat → Option (Boundary.Exception Nat)
  | .pending => none
  | .fulfilled _ => some original
  | .rejected reason => some reason

private def firstReason (old : Option (Boundary.Exception Nat)) (next : Boundary.Exception Nat) :
    Option (Boundary.Exception Nat) :=
  match old with | none => some next | some reason => some reason

private def entryGate (s : Writable.State Nat Nat) : Bool :=
  match s.status with | .writable => !Writable.closeQueuedOrInFlight s | _ => false

private def forwardFirst (r : Readable.Status Nat) (w : Writable.Status Nat) :
    Option (Boundary.Exception Nat) :=
  match r with
  | .errored reason => some reason
  | _ => match w with | .errored reason => some reason | _ => none

private def backwardFirst (r : Readable.Status Nat) (w : Writable.Status Nat) :
    Option (Boundary.Exception Nat) :=
  match w with
  | .errored reason => some reason
  | _ => match r with | .errored reason => some reason | _ => none

private def sourceStart : Readable.State Nat Nat :=
  Readable.initial { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero

private def destinationStart : Writable.State Nat Nat :=
  Writable.initial Writable.sizes.one
    { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
      abort := some (.foreign 2) } 0 0

-- WS-PIPE-CE-001: proceeding immediately violates the outstanding write obligation.
theorem ce001_pending_write_blocks :
    allSettled [.pending] = false ∧ (true : Bool) ≠ allSettled [.pending] := by
  decide +kernel

-- WS-PIPE-CE-002: a rejected write has settled; waiting for fulfillment is stronger and wrong.
theorem ce002_rejected_write_settled :
    allSettled [.rejected (.foreign 2)] = true ∧
    (([.rejected (.foreign 2)] : List (Writable.UnitPromise Nat)).all fulfilled) = false := by
  decide +kernel

-- WS-PIPE-CE-003: the first settled target does not release a two-write wait.
theorem ce003_stale_wait_target :
    allSettled [.fulfilled (), .pending] = false ∧
    settled (.fulfilled ()) = true := by
  decide +kernel

-- WS-PIPE-CE-004: equal chunks remain two obligations because their read IDs differ.
theorem ce004_duplicate_chunk_ids :
    ([(0, 7), (1, 7)] : List (Nat × Nat)).length = 2 ∧
    (([(0, 7), (1, 7)] : List (Nat × Nat)).map Prod.snd).eraseDups.length = 1 := by
  decide +kernel

-- WS-PIPE-CE-005: the current queue cannot reconstruct the already-delivered read.
theorem ce005_queue_drops_read_history :
    let r := Readable.error (Readable.read (Readable.beginEnqueue sourceStart 7)) (.foreign 1)
    r.queue.entries = [] ∧
    r.readPromises = [(0, .fulfilled (.chunk 7))] ∧
    Readable.Event.settled (.read 0 (.ok (.chunk 7))) ∈ r.trace := by
  decide +kernel

-- WS-PIPE-CE-006: a later source/competitor notification cannot replace the selection.
theorem ce006_first_shutdown_wins :
    firstReason (some (.foreign 1)) (.foreign 2) = some (.foreign 1) ∧
    firstReason (some (.foreign 1)) (.foreign 2) ≠ some (.foreign 2) := by
  decide +kernel

-- WS-PIPE-CE-007: preventAbort affects the action, not the preceding required wait.
theorem ce007_prevent_abort_still_waits :
    (if (true : Bool) then allSettled [.pending] else allSettled [.pending]) = false ∧
    (if (true : Bool) then true else allSettled [.pending]) = true := by
  decide +kernel

-- WS-PIPE-CE-008: a write's different error cannot replace the selected source reason.
theorem ce008_write_error_no_override :
    finishReason (.foreign 1) (.fulfilled ()) = some (.foreign 1) ∧
    finishReason (.foreign 1) (.fulfilled ()) ≠ some (.foreign 2) := by
  decide +kernel

-- WS-PIPE-CE-009: the shutdown action's rejection is the replacement reason.
theorem ce009_action_error_overrides :
    finishReason (.foreign 1) (.rejected (.foreign 3)) = some (.foreign 3) ∧
    finishReason (.foreign 1) (.rejected (.foreign 3)) ≠ some (.foreign 1) := by
  decide +kernel

-- WS-PIPE-CE-010: changing destination state after entry cannot erase an owed wait.
theorem ce010_capture_drain_gate :
    entryGate destinationStart = true ∧
    entryGate { destinationStart with status := .errored (.foreign 2) } = false ∧
    (entryGate destinationStart && !allSettled [.pending]) = true ∧
    (entryGate { destinationStart with status := .errored (.foreign 2) } &&
      !allSettled [.pending]) = false := by
  decide +kernel

-- WS-PIPE-CE-011: intrinsic abort on a terminal destination yields a fulfilled result cell.
theorem ce011_terminal_abort_fulfills :
    let w := { destinationStart with
      status := .errored (.foreign 2),
      control := [Writable.Control.beginAbort 0 (.foreign 1)] }
    (Writable.tick w).map (fun t => Writable.lookupPromise t 2) =
      some (some (.fulfilled ())) ∧
    (Writable.tick w).map Writable.State.signalArgument = some none := by
  decide +kernel

-- WS-PIPE-CE-012: queued reactions cannot execute behind a synchronous foreign marker.
theorem ce012_callback_blocks_jobs :
    let w := { destinationStart with
      control := [Writable.Control.awaitSize 0 7],
      jobs := [⟨.write, 2, .fulfilled⟩] }
    Writable.tick w = none := by
  rfl

-- WS-PIPE-CE-013: simultaneous source/destination errors select the source first.
theorem ce013_forward_error_priority :
    forwardFirst (.errored (.foreign 1)) (.errored (.foreign 2)) = some (.foreign 1) ∧
    backwardFirst (.errored (.foreign 1)) (.errored (.foreign 2)) = some (.foreign 2) := by
  decide +kernel

-- WS-PIPE-CE-014: callback return with a pending promise is not action settlement.
theorem ce014_pending_action_is_live :
    finishReason (.foreign 1) .pending = none ∧
    finishReason (.foreign 1) .pending ≠ some (.foreign 1) := by
  decide +kernel

-- WS-PIPE-CE-015: erroring during an owed write's size callback does not remove its result.
-- The first write is pending; a prescribed canonical after-size stage returns the second
-- write as a rejected cell. These are two actual P5 stages, not a whole reentrant tape.
theorem ce015_erroring_owed_write_keeps_wait :
    let w := { destinationStart with
      status := .erroring (.foreign 2),
      algorithms := { size := none, write := none, close := none, abort := none },
      nextCall := 3, nextPromise := 4,
      promises := [(0, .fulfilled ()), (1, .pending), (2, .pending),
        (3, .rejected (.foreign 2))],
      inFlightWrite := some (2, .awaiting),
      control := [Writable.Control.afterSize 1 8 Writable.sizes.one] }
    let returned := (Writable.tick w).bind Writable.tick
    entryGate destinationStart = true ∧ entryGate w = false ∧
    returned.map (fun t => Writable.lookupPromise t 2) = some (some .pending) ∧
    returned.map (fun t => Writable.lookupPromise t 4) = some (some (.rejected (.foreign 2))) ∧
    returned.map (fun t => t.trace.any (fun e => match e with
      | .returned 1 4 => true | _ => false)) = some true ∧
    allSettled [.pending, .rejected (.foreign 2)] = false := by
  decide +kernel

-- WS-PIPE-CE-016: a forbidden read still allocates an ID even on the errored source.
theorem ce016_new_read_changes_snapshot :
    let r := Readable.error sourceStart (.foreign 1)
    (Readable.read r).nextRead = r.nextRead + 1 ∧
    (Readable.read r).nextRead ≠ r.nextRead ∧
    (Readable.read r).readPromises = [(0, .rejected (.foreign 1))] := by
  decide +kernel

#print axioms ce001_pending_write_blocks
#print axioms ce002_rejected_write_settled
#print axioms ce003_stale_wait_target
#print axioms ce004_duplicate_chunk_ids
#print axioms ce005_queue_drops_read_history
#print axioms ce006_first_shutdown_wins
#print axioms ce007_prevent_abort_still_waits
#print axioms ce008_write_error_no_override
#print axioms ce009_action_error_overrides
#print axioms ce010_capture_drain_gate
#print axioms ce011_terminal_abort_fulfills
#print axioms ce012_callback_blocks_jobs
#print axioms ce013_forward_error_priority
#print axioms ce014_pending_action_is_live
#print axioms ce015_erroring_owed_write_keeps_wait
#print axioms ce016_new_read_changes_snapshot

end WhatwgTest.Streams.Counterexamples.Piping
