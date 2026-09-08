import Whatwg.Streams.Semantics.Configuration

/-!
# Semantics.Mask.lean

Owner: the two pre-registered observation masks as declared projections of a
run: M1, the chunk sequence with the terminal outcome, and M2, the full
settlement order.

Spec anchors: none; the `model` section is a reading aid only.

Opened by slice Q4 for its M2 half only. Packet:
`test/contracts/configuration-ordering.contract.md`; graph
`CONFIGURATION-PG-ORDERING`.

Decision 5: a **live finite-prefix** M2 result, with no terminal outcome and no
sink-input field. DB-04 M2 is a repository ruling about claim scope, so it
belongs in no promise library (inventory group G): restating one of these rows
in `Whatwg.Ecma262` or `Whatwg.WebIdl` would be a defect under R-P12. Class [A]
throughout.
-/

namespace Whatwg.Streams.Semantics.Ordering

open Whatwg.Streams

/-- Decision 5: the live prefix admits exactly the four settlement and query
events, and no return. Class [A]. -/
def m2Allowed {ε : Type} (event : Writable.VisibleEvent ε) : Bool :=
  match event with
  | .settled _ _ | .readyRead _ _ | .closedRead _ _ | .desiredSizeRead _ _ => true
  | .returned _ _ | .controllerReturned _ => false

/-- A finite live M2 prefix: an owner, the admitted events in order, and the
proof that nothing else is in it. There is no terminal outcome field, which is
what "live" means (DB-07). Class [A]. -/
structure M2LivePrefix (ε : Type) where
  owner : Nat
  events : List (Writable.VisibleEvent ε)
  allowed : ∀ event ∈ events, m2Allowed event = true

/-- The live projection, defined only inside the admitted profile. Class [A]. -/
def observeLive {α ε : Type} (c : Config α ε) : Option (M2LivePrefix ε) :=
  match c.writable.status with
  | .writable =>
      some ⟨c.owner, (Writable.visibleEvents c.writable).filter m2Allowed,
        fun _ he => (List.mem_filter.mp he).2⟩
  | _ => none

/-! ## Equations -/

/-- Class [A]. Mask M1. -/
theorem m2Allowed_eq {ε : Type} (event : Writable.VisibleEvent ε) :
    m2Allowed event =
      (match event with
      | .settled _ _ | .readyRead _ _ | .closedRead _ _ | .desiredSizeRead _ _ => true
      | .returned _ _ | .controllerReturned _ => false) := by
  cases event <;> rfl

/-- Class [A]. Mask M2. -/
theorem observeLive_writable {α ε : Type} (c : Config α ε) :
    c.writable.status = .writable →
      ∃ p : M2LivePrefix ε,
        observeLive c = some p ∧ p.owner = c.owner ∧
          p.events = (Writable.visibleEvents c.writable).filter m2Allowed := by
  intro h
  refine ⟨⟨c.owner, (Writable.visibleEvents c.writable).filter m2Allowed,
    fun _ he => (List.mem_filter.mp he).2⟩, ?_, rfl, rfl⟩
  unfold observeLive
  rw [h]

/-- Decision 5: outside the admitted profile there is no live prefix at all,
rather than an empty one. Class [A]. Mask M1. -/
theorem observeLive_outside_profile {α ε : Type} (c : Config α ε) :
    c.writable.status ≠ .writable → observeLive c = none := by
  intro h
  unfold observeLive
  cases hs : c.writable.status with
  | writable => exact absurd hs h
  | erroring _ => rfl
  | errored _ => rfl
  | closed => rfl

end Whatwg.Streams.Semantics.Ordering
