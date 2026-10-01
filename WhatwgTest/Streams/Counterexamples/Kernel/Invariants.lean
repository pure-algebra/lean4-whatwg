import Whatwg.Streams

/-!
# Transition-kernel counterexamples `WS-KERNEL-CE-005` and `006`

Breaker-owned witnesses of the W8a packet,
`test/contracts/transition-kernel.contract.md`, section 5; attack shapes in
`test/counterexamples/kernel/ATTACKS.md`; rows in
`test/counterexamples/REGISTER.md`.

Each row is a mutant of one production operation, defined here in the
`Breaker` namespace and never in production. The mutant falsifies the
one-step law the packet freezes for the production operation, at a concrete
state where the law's hypothesis holds; a control shows the production
operation at the same input keeps the invariant.

- `WS-KERNEL-CE-005`: a `Readable.finishEnqueue` that appends the chunk
  without `Data.enqueueValueWithSize`, against `Readable.step_queueInv`.
- `WS-KERNEL-CE-006`: a `Semantics.Ordering.register` that reuses
  `nextObserver - 1` as the new registration identity, against
  `Semantics.Ordering.step_registrationsFresh`.

Red until slice W8a.3 lands `Readable.QueueInv`, `Readable.initial_queueInv`
and `Semantics.Ordering.RegistrationsFresh` with its theorems.

The builder must not change this file.
-/

set_option autoImplicit false
open Whatwg.Streams

namespace WhatwgTest.Streams.Counterexamples.Kernel.Invariants

namespace Breaker

/-- Mutant of `Readable.finishEnqueue`: on a returned size it appends the
entry directly, so neither `[[queueTotalSize]]` nor the admissibility test of
`op.enqueue-value-with-size` runs. The thrown branch is the production one. -/
def finishEnqueueAppend {α ε : Type} (s : Readable.State α ε) (call : Nat) (chunk : α) :
    Data.SizeAnswer Readable.Size (Boundary.Exception ε) → Readable.State α ε
  | .thrown e => Readable.finishEnqueue s call chunk (.thrown e)
  | .value size =>
      Readable.callPullIfNeededWith
        { s with queue := { s.queue with entries := s.queue.entries ++ [⟨chunk, size⟩] } }
        (.returnEnqueue call)

/-- Mutant of `Semantics.Ordering.register`: the new registration takes the
identity `nextObserver - 1`, already issued once the cursor has moved. Every
other step is the production one. -/
def registerReuse {α ε : Type} (c : Semantics.Ordering.Config α ε)
    (p : Whatwg.Ecma262.Promise.Ref) (callback : Nat) :
    Option (Semantics.Ordering.Config α ε) :=
  match Semantics.Ordering.lookup c p with
  | none => none
  | some outcome =>
      let id := c.nextObserver - 1
      let b : Semantics.Ordering.Config α ε :=
        { c with
          registrations :=
            c.registrations ++ [⟨id, p.cell, .fulfill, some callback, none, .waiting⟩],
          nextObserver := id + 1, trace := c.trace ++ [.registered id p callback] }
      match outcome with
      | .pending => some b
      | .fulfilled _ | .rejected _ =>
          let queued := Semantics.Ordering.enqueueJob b (.observer id)
          some (Semantics.Ordering.setRegistrationPhase queued.1 id (.queued queued.2.serial))

end Breaker

/-! ## `WS-KERNEL-CE-005`: the readable queue invariant -/

/-- The smallest positive size on the grid, `2 ^ (-1074)`: one unit. The
witnesses use it rather than `Readable.sizes.one`, which is `2 ^ 1074` units
and does not reduce under `decide`. -/
def unit : Readable.Size := .finite 1

/-- The readable machine after start, with the count strategy and high-water
mark one unit. -/
def readable0 : Readable.State Unit Unit :=
  Readable.initial ⟨.one, 0, 0⟩ unit

/-- Control: the production operation keeps `[[queueTotalSize]]` equal to the
sum of the queued sizes. -/
theorem ce005_reference_wf :
    Data.Queue.WF Readable.sizes (Readable.finishEnqueue readable0 0 () (.value unit)).queue := by
  decide

/-- The mutant leaves the total at zero beside one queued entry of one unit. -/
theorem ce005_mutant_breaks_wf :
    ¬ Data.Queue.WF Readable.sizes
      (Breaker.finishEnqueueAppend readable0 0 () (.value unit)).queue := by
  decide

/-- The one-step law the packet freezes for the production operation fails for
the mutant, at the initial state, where `Readable.initial_queueInv` supplies
the hypothesis. -/
theorem ce005_mutant_breaks_step_law :
    ¬ ∀ (s : Readable.State Unit Unit), Readable.QueueInv s →
        Readable.QueueInv (Breaker.finishEnqueueAppend s 0 () (.value unit)) :=
  fun h => ce005_mutant_breaks_wf (h readable0 (Readable.initial_queueInv _ _)).1

/-! ## `WS-KERNEL-CE-006`: registration identities -/

/-- The configuration at its initial state, with promise cells `0` (ready) and
`1` (closed) under owner `0`. -/
def config0 : Semantics.Ordering.Config Unit Unit :=
  Semantics.Ordering.initial 0 Writable.sizes.one
    ⟨some .one, some .fulfilled, some .fulfilled, some .fulfilled⟩ 0 0

/-- The promise reference both registrations below observe: owner `0`, cell
`1`, the closed promise, which is pending. -/
def closedRef : Whatwg.Ecma262.Promise.Ref := ⟨0, 1⟩

/-- One production registration from the initial configuration: identity `0`,
cursor `1`. -/
def config1 : Semantics.Ordering.Config Unit Unit :=
  (Semantics.Ordering.register config0 closedRef 7).getD config0

theorem ce006_config1_step :
    Semantics.Ordering.Step config0 (some (.observe closedRef 7)) config1 :=
  rfl

/-- The hypothesis of the frozen step law holds at `config1`, from the frozen
initial and step theorems. -/
theorem ce006_config1_fresh : Semantics.Ordering.RegistrationsFresh config1 :=
  Semantics.Ordering.step_registrationsFresh
    (Semantics.Ordering.initial_registrationsFresh _ _ _ _ _) ce006_config1_step

/-- Control: a second production registration takes identity `1`. -/
theorem ce006_reference_ids :
    ((Semantics.Ordering.register config1 closedRef 8).map
        Semantics.Ordering.registrationIds) = some [0, 1] :=
  rfl

/-- The configuration after the mutant's second registration. -/
def mutant2 : Semantics.Ordering.Config Unit Unit :=
  (Breaker.registerReuse config1 closedRef 8).getD config1

theorem ce006_mutant_step : Breaker.registerReuse config1 closedRef 8 = some mutant2 :=
  rfl

/-- The mutant's second registration takes identity `0` again. -/
theorem ce006_mutant_ids : Semantics.Ordering.registrationIds mutant2 = [0, 0] :=
  rfl

/-- The one-step law the packet freezes for the production operation fails for
the mutant, at a configuration one production step from `initial`. -/
theorem ce006_mutant_breaks_step_law :
    ¬ ∀ (c t : Semantics.Ordering.Config Unit Unit) (p : Whatwg.Ecma262.Promise.Ref)
        (callback : Nat),
        Semantics.Ordering.RegistrationsFresh c →
          Breaker.registerReuse c p callback = some t →
            Semantics.Ordering.RegistrationsFresh t := by
  intro h
  have hnd := (h config1 mutant2 closedRef 8 ce006_config1_fresh ce006_mutant_step).1
  rw [ce006_mutant_ids] at hnd
  exact absurd hnd (by decide)

end WhatwgTest.Streams.Counterexamples.Kernel.Invariants
