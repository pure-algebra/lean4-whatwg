import Whatwg.Streams

/-!
# Transition-kernel counterexamples `WS-KERNEL-CE-001` to `004`

Breaker-owned witnesses of the W8a packet,
`test/contracts/transition-kernel.contract.md`; attack shapes in
`test/counterexamples/kernel/ATTACKS.md`; rows in
`test/counterexamples/REGISTER.md`.

Each row shows that a hypothesis or a form the packet freezes is
load-bearing: dropping it yields a false statement, witnessed here.

- `WS-KERNEL-CE-001`: `Kernel.Path.deterministic` needs `Kernel.Deterministic`.
- `WS-KERNEL-CE-002`: `Kernel.prefix_comparable` needs `Kernel.Exclusive`, and
  the local Writable machine is not exclusive, so the law does not transfer
  to `Writable.Reaches`.
- `WS-KERNEL-CE-003`: `Kernel.normalized_unique` needs both ends normalized,
  even under exclusivity.
- `WS-KERNEL-CE-004`: the two-stage bridges are pointwise iffs, because an
  equation of relations does not close by `rfl` at an open label.

Red until slice W8a.1 lands `Whatwg.Streams.Kernel`: every row names a kernel
constant. Nothing here needs a name of W8a.2 or W8a.3. The toy relations live
in the `Breaker` namespace and are not production declarations.

The builder must not change this file.
-/

set_option autoImplicit false
open Whatwg.Streams

namespace WhatwgTest.Streams.Counterexamples.Kernel.Path

namespace Breaker

/-- Every state steps to every state under the one label. -/
def anyStep : Bool → Unit → Bool → Prop := fun _ _ _ => True

/-- A non-exclusive two-stage toy: at state 0 the deterministic stage moves to
1 and the decision `()` is also admitted, to 2. -/
def forkTick : Nat → Option Nat
  | 0 => some 1
  | 2 => some 4
  | _ => none

def forkAccept : Nat → Unit → Option Nat
  | 0, _ => some 2
  | 1, _ => some 3
  | _, _ => none

/-- An exclusive two-stage toy that admits no decision at all: the
deterministic stage moves from 0 to 1 and stops. -/
def countTick : Nat → Option Nat
  | 0 => some 1
  | _ => none

def countAccept : Nat → Unit → Option Nat := fun _ _ => none

end Breaker

/-! ## `WS-KERNEL-CE-001`: determinism is a hypothesis -/

theorem ce001_not_deterministic : ¬ Kernel.Deterministic Breaker.anyStep :=
  fun h => absurd (h false () false true trivial trivial) (by decide)

/-- One label list, two derivations from one start, two distinct ends. -/
theorem ce001_two_ends :
    Kernel.Path Breaker.anyStep false [()] false ∧
      Kernel.Path Breaker.anyStep false [()] true :=
  ⟨Kernel.Path.single trivial, Kernel.Path.single trivial⟩

/-- The conclusion of `Kernel.Path.deterministic`, without its hypothesis, is
false. -/
theorem ce001_unconditional_false :
    ¬ ∀ {s t u : Bool} {ds : List Unit},
        Kernel.Path Breaker.anyStep s ds t → Kernel.Path Breaker.anyStep s ds u → t = u :=
  fun h => absurd (h ce001_two_ends.1 ce001_two_ends.2) (by decide)

/-! ## `WS-KERNEL-CE-002`: exclusivity is a hypothesis, and Writable lacks it -/

theorem ce002_fork_not_exclusive : ¬ Kernel.Exclusive Breaker.forkTick Breaker.forkAccept :=
  fun h => absurd (h 0 1 () rfl) (by decide)

/-- Silent step then decision, `0 → 1 → 3`. -/
theorem ce002_left :
    Kernel.Path (Kernel.Graph (Kernel.stage Breaker.forkTick Breaker.forkAccept))
      0 [none, some ()] 3 :=
  Kernel.Path.cons rfl (Kernel.Path.single rfl)

/-- Decision then silent step, `0 → 2 → 4`. -/
theorem ce002_right :
    Kernel.Path (Kernel.Graph (Kernel.stage Breaker.forkTick Breaker.forkAccept))
      0 [some (), none] 4 :=
  Kernel.Path.cons rfl (Kernel.Path.single rfl)

/-- The conclusion of `Kernel.prefix_comparable`, without exclusivity, is
false: the two derivations consume the same external word `[()]`, and their
ends `3` and `4` are both stuck and distinct, so neither reaches the other by
silent steps. -/
theorem ce002_comparability_false :
    ¬ ∀ (left right : List (Option Unit)) (s t u : Nat),
        Kernel.Path (Kernel.Graph (Kernel.stage Breaker.forkTick Breaker.forkAccept)) s left t →
          Kernel.Path (Kernel.Graph (Kernel.stage Breaker.forkTick Breaker.forkAccept)) s right u →
            Kernel.externalWord left = Kernel.externalWord right →
              (∃ n : Nat,
                  Kernel.Path (Kernel.Graph (Kernel.stage Breaker.forkTick Breaker.forkAccept)) t
                    (List.replicate n none) u) ∨
                ∃ n : Nat,
                  Kernel.Path (Kernel.Graph (Kernel.stage Breaker.forkTick Breaker.forkAccept)) u
                    (List.replicate n none) t := by
  intro h
  rcases h [none, some ()] [some (), none] 0 3 4 ce002_left ce002_right rfl with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact absurd (Kernel.silent_stuck n rfl hn) (by decide)
  · exact absurd (Kernel.silent_stuck n rfl hn) (by decide)

/-- The production half: the local Writable machine is not exclusive. At an
empty control stack with one queued sink job, `Writable.tick` runs the job and
`Writable.decide` still admits `queryReady`. This is why the configuration
exists, and why `Kernel.prefix_comparable` does not transfer to
`Writable.Reaches`. -/
theorem ce002_writable_not_exclusive :
    ¬ Kernel.Exclusive (@Writable.tick Unit Unit) Writable.decide := by
  intro h
  let s : Writable.State Unit Unit :=
    { Writable.initial Writable.sizes.one
        ⟨some .one, some .fulfilled, some .fulfilled, some .fulfilled⟩ 0 0 with
      jobs := [⟨.write, 0, .fulfilled⟩] }
  have ht : Writable.tick s =
      some { s with control := [.react ⟨.write, 0, .fulfilled⟩], jobs := [] } := rfl
  have hd := h s _ .queryReady ht
  exact nomatch hd

/-! ## `WS-KERNEL-CE-003`: normalized ends are a hypothesis -/

theorem ce003_exclusive : Kernel.Exclusive Breaker.countTick Breaker.countAccept :=
  fun _ _ _ _ => rfl

/-- The conclusion of `Kernel.normalized_unique` without `tick t = none` and
`tick u = none` is false, even under exclusivity: the empty derivation ends at
`0` and the one-silent-step derivation at `1`, with one external word `[]`,
and `0` is not normalized. -/
theorem ce003_unnormalized_false :
    ¬ ∀ {s t u : Nat} {left right : List (Option Unit)},
        Kernel.Path (Kernel.Graph (Kernel.stage Breaker.countTick Breaker.countAccept))
          s left t →
          Kernel.Path (Kernel.Graph (Kernel.stage Breaker.countTick Breaker.countAccept))
            s right u →
            Kernel.externalWord left = Kernel.externalWord right → t = u := by
  intro h
  have hl : Kernel.Path (Kernel.Graph (Kernel.stage Breaker.countTick Breaker.countAccept))
      0 [] 0 := Kernel.Path.nil 0
  have hr : Kernel.Path (Kernel.Graph (Kernel.stage Breaker.countTick Breaker.countAccept))
      0 [none] 1 := Kernel.Path.single rfl
  exact absurd (h hl hr rfl) (by decide)

/-- Control: the start is not normalized, and the comparability law does hold
of the same pair, with one silent step between the ends. -/
theorem ce003_start_not_normalized : Breaker.countTick 0 ≠ none := by decide

theorem ce003_comparable :
    Kernel.Path (Kernel.Graph (Kernel.stage Breaker.countTick Breaker.countAccept))
      0 (List.replicate 1 none) 1 :=
  Kernel.Path.single rfl

/-! ## `WS-KERNEL-CE-004`: the two-stage bridge is not an equation by `rfl`

`Writable.Step` matches on the label inside its own body; `Kernel.stage`
matches in its own equations. At an open label the elaborator does not
identify the two matchers, so the equation of relations does not close by
`rfl`, and the frozen bridge is the pointwise iff `Writable.step_iff_stage`,
proved by cases on the label. The diagnostic is not pinned: the assertion is
only that the term does not elaborate. -/

#guard_msgs (drop info) in
#check_failure (fun (s : Writable.State Unit Unit) (d : Option (Writable.Decision Unit Unit))
    (t : Writable.State Unit Unit) =>
  (rfl : Writable.Step s d t =
    Kernel.Graph (Kernel.stage Writable.tick Writable.decide) s d t))

/-- Control: at each closed label the same equation is `rfl`, which is why the
bridge is proved by `cases d`. -/
example (s : Writable.State Unit Unit) (t : Writable.State Unit Unit) :
    Writable.Step s none t = Kernel.Graph (Kernel.stage Writable.tick Writable.decide) s none t :=
  rfl

example (s : Writable.State Unit Unit) (a : Writable.Decision Unit Unit)
    (t : Writable.State Unit Unit) :
    Writable.Step s (some a) t =
      Kernel.Graph (Kernel.stage Writable.tick Writable.decide) s (some a) t :=
  rfl

end WhatwgTest.Streams.Counterexamples.Kernel.Path
