import Whatwg.Streams

/-!
Breaker-owned W8a battery: the queue invariant of the default-writable
machine, an additive amendment of the P5a contract.

Contracts: `test/contracts/transition-kernel.contract.md`, section 5, and the
dated W8a amendment at the end of `test/contracts/writable-default.contract.md`.
Design: `docs/research/2026-10-01-w8-transition-kernel-design.md`, section
2.7. Ruling: R-W4.
Graph: WRITABLE-PG-DEFAULT, construction edge.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

`Writable.QueueInv` is the queue-with-sizes invariant of DATA-PG-QUEUE
(`Data.Queue.WF` and `Data.Queue.SizesAdmissible` at `Writable.sizes`) read
off the writable machine's `[[queue]]`. It is inductive: neither stage needs
a reachability hypothesis. The closure theorem is carried by
`Kernel.Path.invariant` through `Writable.reaches_iff_path`.

Six ascriptions and one body pin. No earlier P5a ascription changes.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

#check (@Writable.QueueInv : {α ε : Type} → Writable.State α ε → Prop)

-- Body pin: the two queue-with-sizes predicates at the writable size class.
example {α ε : Type} (s : Writable.State α ε) :
    Writable.QueueInv s =
      (Data.Queue.WF Writable.sizes s.queue ∧
        Data.Queue.SizesAdmissible Writable.sizes s.queue) :=
  rfl

#check (@Writable.tick_queueInv :
  ∀ {α ε : Type} (s t : Writable.State α ε),
    Writable.QueueInv s → Writable.tick s = some t → Writable.QueueInv t)

#check (@Writable.decide_queueInv :
  ∀ {α ε : Type} (s t : Writable.State α ε) (d : Writable.Decision α ε),
    Writable.QueueInv s → Writable.decide s d = some t → Writable.QueueInv t)

#check (@Writable.step_queueInv :
  ∀ {α ε : Type} {s t : Writable.State α ε} {d : Option (Writable.Decision α ε)},
    Writable.QueueInv s → Writable.Step s d t → Writable.QueueInv t)

#check (@Writable.reaches_queueInv :
  ∀ {α ε : Type} {s t : Writable.State α ε} {ds : List (Option (Writable.Decision α ε))},
    Writable.Reaches s ds t → Writable.QueueInv s → Writable.QueueInv t)

#check (@Writable.initial_queueInv :
  ∀ {α ε : Type} (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat),
    Writable.QueueInv (Writable.initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed))
