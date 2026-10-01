import Whatwg.Streams
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned W8a battery: freshness of registration identities in the
configuration, an additive amendment of the Q4 contract.

Contracts: `test/contracts/transition-kernel.contract.md`, section 5, and the
dated W8a amendment at the end of
`test/contracts/configuration-ordering.contract.md`.
Design: `docs/research/2026-10-01-w8-transition-kernel-design.md`, section
2.7. Ruling: R-W4.
Graph: CONFIGURATION-PG-ORDERING, construction edge.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

`Ordering.RegistrationsFresh` says the registration identities are
duplicate-free and below the observer cursor `nextObserver`. Freshness alone
is not inductive; with the cursor bound it is, so the step theorem has no
reachability hypothesis. `reachable_registrations_nodup` discharges the
`Nodup` premise that `notifySettled_reactions_bridge` and
`notifySettled_queued_serial` carry (amendment A4 of the Q4 contract) at every
configuration reachable from `initial`. The predicate is the first clause of
the held P8a draft's `SerialsWellFormed`; `CellsWellFormed` is not here and
stays with P8 (CFG-CELLS).

Six ascriptions and two body pins. No earlier Q4 ascription changes.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

#whatwg_freeze (@Semantics.Ordering.registrationIds :
  {α ε : Type} → Semantics.Ordering.Config α ε → List Nat)

-- Body pin: the registration identities, in registration order.
example {α ε : Type} (c : Semantics.Ordering.Config α ε) :
    Semantics.Ordering.registrationIds c = c.registrations.map (fun r => r.id) :=
  rfl

#whatwg_freeze (@Semantics.Ordering.RegistrationsFresh :
  {α ε : Type} → Semantics.Ordering.Config α ε → Prop)

-- Body pin: duplicate-free, and every identity below the observer cursor.
example {α ε : Type} (c : Semantics.Ordering.Config α ε) :
    Semantics.Ordering.RegistrationsFresh c =
      ((Semantics.Ordering.registrationIds c).Nodup ∧
        ∀ i ∈ Semantics.Ordering.registrationIds c, i < c.nextObserver) :=
  rfl

#whatwg_freeze (@Semantics.Ordering.step_registrationsFresh :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)},
    Semantics.Ordering.RegistrationsFresh c → Semantics.Ordering.Step c d t →
      Semantics.Ordering.RegistrationsFresh t) axioms [propext, Quot.sound]

#whatwg_freeze (@Semantics.Ordering.reaches_registrationsFresh :
  ∀ {α ε : Type} {c t : Semantics.Ordering.Config α ε}
    {ds : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Reaches c ds t → Semantics.Ordering.RegistrationsFresh c →
      Semantics.Ordering.RegistrationsFresh t) axioms [propext, Quot.sound]

#whatwg_freeze (@Semantics.Ordering.initial_registrationsFresh :
  ∀ {α ε : Type} (owner : Nat) (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat),
    Semantics.Ordering.RegistrationsFresh
      (Semantics.Ordering.initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed)) axioms [propext]

#whatwg_freeze (@Semantics.Ordering.reachable_registrations_nodup :
  ∀ {α ε : Type} {c : Semantics.Ordering.Config α ε} {owner : Nat} {hwm : Writable.Size}
    {alg : Writable.Algorithms} {promiseSeed errorSeed : Nat}
    {ds : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Reaches
        (Semantics.Ordering.initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed)
        ds c →
      (c.registrations.map (fun r => r.id)).Nodup) axioms [propext, Quot.sound]
