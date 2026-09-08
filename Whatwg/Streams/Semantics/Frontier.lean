import Whatwg.Streams.Semantics.Configuration

/-!
# Semantics.Frontier.lean

Owner: live frontiers: fuel exhaustion and an unanswered decision, each kept
apart from typed failure, cancellation, abort and refusal.

Spec anchors: none; the `model` section is a reading aid only.

Opened by slice Q4 for the successful-control grammar of the held P8a draft.
Packet: `test/contracts/configuration-ordering.contract.md`; graph
`CONFIGURATION-PG-ORDERING`.

These are predicates on the actual P5 `Writable.Control` list and nothing in
them is promise-layer content: they describe which suspended control stacks the
admitted all-successful pre-start profile of decision 3 can reach, which is
what makes an unanswered foreign call a live frontier rather than a failure
(DB-07). Class [A] throughout.
-/

namespace Whatwg.Streams.Semantics.Ordering

open Whatwg.Streams

/-- The write requests whose promise has been staged but not yet returned.
Class [A]. -/
def stagedRequests {α ε : Type} : List (Writable.Control α ε) → List Nat
  | .enqueueWrite _ _ :: .returnPromise _ id :: rest => id :: stagedRequests rest
  | _ :: rest => stagedRequests rest
  | [] => []

/-- How many suspended sink calls the stack carries. Class [A]. -/
def sinkMarkerCount {α ε : Type} (control : List (Writable.Control α ε)) : Nat :=
  (control.filter (fun frame => match frame with | .awaitSink _ => true | _ => false)).length

/-- The suspended stacks the admitted profile reaches: nested size calls above
at most one suspended sink write. Class [A]. -/
inductive Suspensions {α ε : Type} : List (Writable.Control α ε) → Prop
  | nil : Suspensions []
  | size (call : Nat) (chunk : α) {rest : List (Writable.Control α ε)} :
      Suspensions rest → Suspensions (.awaitSize call chunk :: rest)
  | sinkIntrinsic (request : Nat) (chunk : α) :
      Suspensions (ε := ε) [.awaitSink (.write request chunk)]
  | sinkCall (request : Nat) (chunk : α) (call id : Nat)
      {rest : List (Writable.Control α ε)} :
      Suspensions rest → sinkMarkerCount rest = 0 →
        Suspensions (.awaitSink (.write request chunk) :: .returnPromise call id :: rest)

/-- One administrative frame above a suspended stack: the shapes the
all-successful pre-start profile of decision 3 can be in. Class [A]. -/
inductive SuccessfulControl {α ε : Type} : List (Writable.Control α ε) → Prop
  | suspended {rest : List (Writable.Control α ε)} :
      Suspensions rest → SuccessfulControl rest
  | getSize (call : Nat) (chunk : α) {rest : List (Writable.Control α ε)} :
      Suspensions rest → SuccessfulControl (.getSize call chunk :: rest)
  | afterSize (call : Nat) (chunk : α) (size : Writable.Size)
      {rest : List (Writable.Control α ε)} :
      Suspensions rest → SuccessfulControl (.afterSize call chunk size :: rest)
  | enqueue (chunk : α) (size : Writable.Size) (call id : Nat)
      {rest : List (Writable.Control α ε)} :
      Suspensions rest →
        SuccessfulControl (.enqueueWrite chunk size :: .returnPromise call id :: rest)
  | advanceCall (call id : Nat) {rest : List (Writable.Control α ε)} :
      Suspensions rest → SuccessfulControl (.advance :: .returnPromise call id :: rest)
  | returnPromise (call id : Nat) {rest : List (Writable.Control α ε)} :
      Suspensions rest → SuccessfulControl (.returnPromise call id :: rest)
  | advanceIntrinsic : SuccessfulControl (α := α) (ε := ε) [.advance]
  | react (job : Writable.SinkJob α ε) : SuccessfulControl [.react job]

/-! ## Equations — mask M1 -/

/-- Class [A]. Mask M1. -/
theorem stagedRequests_nil {α ε : Type} :
    stagedRequests (α := α) (ε := ε) [] = [] := rfl

/-- Class [A]. Mask M1. -/
theorem stagedRequests_pair {α ε : Type} (chunk : α) (size : Writable.Size) (call id : Nat)
    (rest : List (Writable.Control α ε)) :
    stagedRequests (.enqueueWrite chunk size :: .returnPromise call id :: rest) =
      id :: stagedRequests rest := rfl

/-- Class [A]. Mask M1. -/
theorem stagedRequests_other {α ε : Type} (head : Writable.Control α ε)
    (rest : List (Writable.Control α ε)) :
    (∀ (chunk : α) (size : Writable.Size) (call id : Nat)
      (tail : List (Writable.Control α ε)),
      head :: rest ≠ .enqueueWrite chunk size :: .returnPromise call id :: tail) →
      stagedRequests (head :: rest) = stagedRequests rest := by
  intro h
  cases head <;> try rfl
  rename_i chunk size
  cases rest <;> try rfl
  rename_i head' rest'
  cases head' <;> try rfl
  rename_i call id
  exact absurd rfl (h chunk size call id rest')

/-- Class [A]. Mask M1. -/
theorem sinkMarkerCount_eq {α ε : Type} (control : List (Writable.Control α ε)) :
    sinkMarkerCount control =
      (control.filter (fun frame => match frame with | .awaitSink _ => true | _ => false)).length :=
  rfl

/-- Class [A]. A suspended stack stages nothing. Mask M1. -/
theorem suspensions_staged_empty {α ε : Type} {rest : List (Writable.Control α ε)} :
    Suspensions rest → stagedRequests rest = [] := by
  intro h
  induction h <;> first | rfl | assumption

/-- Class [A]. Decision 3: at most one sink call is suspended. Mask M1. -/
private theorem suspensions_sink_count {α ε : Type} {control : List (Writable.Control α ε)} :
    Suspensions control → sinkMarkerCount control ≤ 1 := by
  intro h
  induction h with
  | nil => simp [sinkMarkerCount]
  | size _ _ _ ih => simpa [sinkMarkerCount] using ih
  | sinkIntrinsic _ _ => simp [sinkMarkerCount]
  | sinkCall _ _ _ _ _ hcount ih =>
      simp only [sinkMarkerCount, List.filter_cons] at hcount ⊢
      simp_all

/-- Class [A]. Mask M1. -/
theorem successfulControl_advance_staged_empty {α ε : Type}
    {rest : List (Writable.Control α ε)} :
    SuccessfulControl (.advance :: rest) → stagedRequests (.advance :: rest) = [] := by
  intro h
  cases h <;>
    first
      | rfl
      | (rename_i hs; have hstaged := suspensions_staged_empty hs; exact hstaged)

/-- Class [A]. Decision 3. Mask M1. -/
theorem successfulControl_sink_at_most_one {α ε : Type}
    {control : List (Writable.Control α ε)} :
    SuccessfulControl control → sinkMarkerCount control ≤ 1 := by
  intro h
  cases h <;>
    first
      | (simp [sinkMarkerCount]; done)
      | (rename_i hs; simpa [sinkMarkerCount] using suspensions_sink_count hs)

/-- Class [A]. The inductive predicate as a closed characterization. Mask M1. -/
theorem suspensions_iff {α ε : Type} (control : List (Writable.Control α ε)) :
    Suspensions control ↔
      control = [] ∨
      (∃ (call : Nat) (chunk : α) (rest : List (Writable.Control α ε)),
        control = .awaitSize call chunk :: rest ∧ Suspensions rest) ∨
      (∃ (request : Nat) (chunk : α), control = [.awaitSink (.write request chunk)]) ∨
      (∃ (request : Nat) (chunk : α) (call id : Nat) (rest : List (Writable.Control α ε)),
        control = .awaitSink (.write request chunk) :: .returnPromise call id :: rest ∧
          Suspensions rest ∧ sinkMarkerCount rest = 0) := by
  constructor
  · intro h
    cases h with
    | nil => exact Or.inl rfl
    | size call chunk hs => exact Or.inr (Or.inl ⟨call, chunk, _, rfl, hs⟩)
    | sinkIntrinsic request chunk => exact Or.inr (Or.inr (Or.inl ⟨request, chunk, rfl⟩))
    | sinkCall request chunk call id hs hcount =>
        exact Or.inr (Or.inr (Or.inr ⟨request, chunk, call, id, _, rfl, hs, hcount⟩))
  · rintro (rfl | ⟨call, chunk, rest, rfl, hs⟩ | ⟨request, chunk, rfl⟩ |
      ⟨request, chunk, call, id, rest, rfl, hs, hcount⟩)
    · exact .nil
    · exact .size call chunk hs
    · exact .sinkIntrinsic request chunk
    · exact .sinkCall request chunk call id hs hcount

/-- Class [A]. The inductive predicate as a closed characterization. Mask M1. -/
theorem successfulControl_iff {α ε : Type} (control : List (Writable.Control α ε)) :
    SuccessfulControl control ↔
      Suspensions control ∨
      (∃ (call : Nat) (chunk : α) (rest : List (Writable.Control α ε)),
        control = .getSize call chunk :: rest ∧ Suspensions rest) ∨
      (∃ (call : Nat) (chunk : α) (size : Writable.Size) (rest : List (Writable.Control α ε)),
        control = .afterSize call chunk size :: rest ∧ Suspensions rest) ∨
      (∃ (chunk : α) (size : Writable.Size) (call id : Nat)
        (rest : List (Writable.Control α ε)),
        control = .enqueueWrite chunk size :: .returnPromise call id :: rest ∧
          Suspensions rest) ∨
      (∃ (call id : Nat) (rest : List (Writable.Control α ε)),
        control = .advance :: .returnPromise call id :: rest ∧ Suspensions rest) ∨
      (∃ (call id : Nat) (rest : List (Writable.Control α ε)),
        control = .returnPromise call id :: rest ∧ Suspensions rest) ∨
      control = [.advance] ∨
      (∃ job : Writable.SinkJob α ε, control = [.react job]) := by
  constructor
  · intro h
    cases h with
    | suspended hs => exact Or.inl hs
    | getSize call chunk hs => exact Or.inr (Or.inl ⟨call, chunk, _, rfl, hs⟩)
    | afterSize call chunk size hs => exact Or.inr (Or.inr (Or.inl ⟨call, chunk, size, _, rfl, hs⟩))
    | enqueue chunk size call id hs =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨chunk, size, call, id, _, rfl, hs⟩)))
    | advanceCall call id hs =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨call, id, _, rfl, hs⟩))))
    | returnPromise call id hs =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨call, id, _, rfl, hs⟩)))))
    | advanceIntrinsic =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    | react job =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨job, rfl⟩))))))
  · rintro (hs | ⟨call, chunk, rest, rfl, hs⟩ | ⟨call, chunk, size, rest, rfl, hs⟩ |
      ⟨chunk, size, call, id, rest, rfl, hs⟩ | ⟨call, id, rest, rfl, hs⟩ |
      ⟨call, id, rest, rfl, hs⟩ | rfl | ⟨job, rfl⟩)
    · exact .suspended hs
    · exact .getSize call chunk hs
    · exact .afterSize call chunk size hs
    · exact .enqueue chunk size call id hs
    · exact .advanceCall call id hs
    · exact .returnPromise call id hs
    · exact .advanceIntrinsic
    · exact .react job

end Whatwg.Streams.Semantics.Ordering
