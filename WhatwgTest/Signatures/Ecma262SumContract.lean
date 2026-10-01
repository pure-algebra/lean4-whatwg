import Whatwg
import Effects.Algebra.Sum
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned Q5b battery for builder slice B6: the face law
`interpret_sumHandler_inr`, the mirror of the landed `interpret_sumHandler_inl`
(gap K of the Q5b addendum).

Packet: `test/contracts/promise-agent-q5.contract.md`, section "Addendum
Q5b". Graph: `PROMISE-PG-AGENT`, `docs/PROMISE-AGENT-DAG.md`. Debt D65.

The ascription names a declaration that does not exist at `5999363`: this
module is red until builder slice B6 adds `interpret_sumHandler_inr` to
`Whatwg/Signatures/Ecma262.lean`. Nothing of Q5 changes. The face imports
`Effects.Algebra.Sum` and nothing else from the `effects` package; this
battery imports it itself only so that its consumer-side half elaborates on
its own.

`Effects.interpret_inr (handlerAt view update) other p` proves the statement
by `exact` today, but `rw` does not see through `sumHandler`, and a consumer
that sums the agent with its own signature needs the equation stated at
`sumHandler`, as `interpret_sumHandler_inl` states the other half. The face
has no census row; masks are DB-04's, and every face law is DB-04 M2.
-/

set_option autoImplicit false

open Whatwg.Ecma262

/-! ## 1. The law

A consumer program, injected into the sum by `Effects.Program.inr`, is
interpreted by the consumer's own handler `other` alone: the agent's lens
handler takes no step, so the summed handler adds nothing to what `other`
does. DB-04 M2. -/

#whatwg_freeze (@Whatwg.Signatures.Ecma262.interpret_sumHandler_inr :
  ∀ {value reason body σ α : Type} {T : Effects.Signature.{0, 0}}
    (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ) (other : Effects.Handler T (StateT σ Id))
    (p : Effects.Program T α),
    Effects.interpret (Whatwg.Signatures.Ecma262.sumHandler view update other)
        (Effects.Program.inr (S := Whatwg.Signatures.Ecma262.signature value reason body) p) =
      Effects.interpret other p) axioms [propext, Quot.sound]

namespace WhatwgTest.Signatures.Ecma262SumContract

/-! ## 2. The shape a consumer writes

The toy second signature of the Q5 face battery, again: a counter in the
second component of the consumer's state `Agent × Nat`, the agent in the
first. -/

/-- The consumer's one operation: read the counter and bump it. -/
inductive TickOp where
  | tick

/-- The consumer's signature, an `abbrev` like the face's. -/
abbrev Tick : Effects.Signature.{0, 0} := ⟨TickOp, fun _ => Nat⟩

/-- The consumer's state. -/
abbrev World : Type := Agent.Agent Unit Nat Nat × Nat

/-- The consumer's own handler. -/
def tickHandler : Effects.Handler Tick (StateT World Id) :=
  ⟨fun _ s => (s.2, (s.1, s.2 + 1))⟩

/-- The view and update of the lens. -/
def view : World → Agent.Agent Unit Nat Nat := Prod.fst
def update : Agent.Agent Unit Nat Nat → World → World := fun a s => (a, s.2)

/-- The summed handler. -/
def both :
    Effects.Handler (Effects.Signature.sum (Whatwg.Signatures.Ecma262.signature Unit Nat Nat) Tick)
      (StateT World Id) :=
  Whatwg.Signatures.Ecma262.sumHandler view update tickHandler

/-- Two ticks, as a consumer program. -/
def twoTicks : Effects.Program Tick Nat :=
  Effects.Program.bind (Effects.Program.perform TickOp.tick)
    (fun m => Effects.Program.bind (Effects.Program.perform TickOp.tick)
      (fun n => Effects.Program.pure (m + n)))

/-- `interpret_sumHandler_inr` at the consumer's instance. -/
example :
    Effects.interpret both
        (Effects.Program.inr (S := Whatwg.Signatures.Ecma262.signature Unit Nat Nat) twoTicks) =
      Effects.interpret tickHandler twoTicks :=
  Whatwg.Signatures.Ecma262.interpret_sumHandler_inr view update tickHandler twoTicks

/-- What it computes: the two ticks answer `5` and `6`, the counter ends at
`7`, and the agent is the one the run started with. -/
example :
    Id.run ((Effects.interpret both
        (Effects.Program.inr (S := Whatwg.Signatures.Ecma262.signature Unit Nat Nat)
          twoTicks)).run (Agent.empty, 5)) =
      (11, (Agent.empty, 7)) := rfl

/-- A mixed program, consumer half first: one tick, then "a promise resolved
with" on the agent side. The tick leaves the agent alone, and the agent's
half is the face's own `run` written back through the lens. -/
def mixed :
    Effects.Program (Effects.Signature.sum (Whatwg.Signatures.Ecma262.signature Unit Nat Nat) Tick)
      (Nat × Promise.Capability) :=
  Effects.Program.bind
    (Effects.Program.inr (S := Whatwg.Signatures.Ecma262.signature Unit Nat Nat)
      (Effects.Program.perform TickOp.tick))
    (fun n => Effects.Program.bind
      (Effects.Program.inl (T := Tick) (Whatwg.Signatures.Ecma262.resolvedWith ()))
      (fun cap => Effects.Program.pure (n, cap)))

example :
    Id.run ((Effects.interpret both mixed).run (Agent.empty, 5)) =
      ((5, (Whatwg.Signatures.Ecma262.run
            (Whatwg.Signatures.Ecma262.resolvedWith (body := Nat) ())
            (Agent.empty : Agent.Agent Unit Nat Nat)).1),
        ((Whatwg.Signatures.Ecma262.run
            (Whatwg.Signatures.Ecma262.resolvedWith (body := Nat) ())
            (Agent.empty : Agent.Agent Unit Nat Nat)).2, 6)) := rfl

end WhatwgTest.Signatures.Ecma262SumContract
