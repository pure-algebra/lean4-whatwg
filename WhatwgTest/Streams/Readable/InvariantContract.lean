import Whatwg.Streams
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned W8a battery: the queue invariant of the default-readable
machine, an additive amendment of the P4a contract.

Contracts: `test/contracts/transition-kernel.contract.md`, section 5, and the
dated W8a amendment at the end of `test/contracts/readable-default.contract.md`.
Design: `docs/research/2026-10-01-w8-transition-kernel-design.md`, section
2.7. Ruling: R-W4.
Graph: READABLE-PG-DEFAULT, construction edge.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

`Readable.QueueInv` is the queue-with-sizes invariant of DATA-PG-QUEUE
(`Data.Queue.WF` and `Data.Queue.SizesAdmissible` at `Readable.sizes`) read
off the readable machine's `[[queue]]`. It is inductive: the step theorem has
no reachability hypothesis. The closure theorem is carried by
`Kernel.Path.invariant` through `Readable.steps_iff_path`.

Four ascriptions and one body pin. No earlier P4a ascription changes.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

#whatwg_freeze (@Readable.QueueInv : {α ε : Type} → Readable.State α ε → Prop)

-- Body pin: the two queue-with-sizes predicates at the readable size class.
example {α ε : Type} (s : Readable.State α ε) :
    Readable.QueueInv s =
      (Data.Queue.WF Readable.sizes s.queue ∧
        Data.Queue.SizesAdmissible Readable.sizes s.queue) :=
  rfl

#whatwg_freeze (@Readable.step_queueInv :
  ∀ {α ε : Type} {s t : Readable.State α ε} {d : Readable.Decision α ε},
    Readable.QueueInv s → Readable.Step s d t → Readable.QueueInv t) axioms [propext, Quot.sound]

#whatwg_freeze (@Readable.steps_queueInv :
  ∀ {α ε : Type} {s t : Readable.State α ε} {ds : List (Readable.Decision α ε)},
    Readable.Steps s ds t → Readable.QueueInv s → Readable.QueueInv t) axioms [propext, Quot.sound]

#whatwg_freeze (@Readable.initial_queueInv :
  ∀ {α ε : Type} (algorithms : Readable.Algorithms) (hwm : Readable.Size),
    Readable.QueueInv (Readable.initial (α := α) (ε := ε) algorithms hwm)) axioms [propext]
