/-!
# Whatwg.Svg.Data.Universe

A finite universe: a type with a list that holds every value at its own index (point T4 and
rule M7 of `docs/SVG-PACKAGE-PLAN.md`, section 3.1). The schema's enumerations are its
instances, in `Whatwg/Svg/Schema/Universe.lean`. A set over a universe is a `Mask`, whose bit
`i` is the value of index `i`.

The one law of the class, `all_index`, gives the three facts that every use needs: `all` holds
every value, an index is below the length, and the index is injective. `forall_of_all` is
reflection, proved once: a Boolean predicate that holds on the list holds at every value
(node U1 of the plan's section 6).

This module names no schema. It does not say that `all` holds a value once: no use reads that,
and a battery counts each census.
-/

namespace Whatwg.Svg.Data

/-- A finite universe: `all` lists every value at its index. -/
class Universe (α : Type) where
  /-- Every value, in index order. -/
  all : List α
  /-- A value's place in `all`. -/
  index : α → Nat
  /-- `all` holds each value at its index. -/
  all_index : ∀ a, all[index a]? = some a

namespace Universe

variable {α : Type} [Universe α]

/-- `all` holds every value. -/
theorem mem_all (a : α) : a ∈ all (α := α) := List.mem_of_getElem? (all_index a)

/-- An index is below the length of `all`. -/
theorem index_lt (a : α) : index a < (all (α := α)).length :=
  (List.getElem?_eq_some_iff.mp (all_index a)).1

/-- Two values with one index are one value. -/
theorem index_injective {a b : α} (h : index a = index b) : a = b := by
  have ha := all_index a
  rw [h, all_index b] at ha
  exact (Option.some.inj ha).symm

/-- Reflection: a Boolean predicate that `List.all` accepts on `all` holds at every value. -/
theorem forall_of_all (p : α → Bool) (h : (all (α := α)).all p = true) (a : α) : p a = true :=
  List.all_eq_true.mp h a (mem_all a)

/-- The same reflection for a decidable proposition. -/
theorem forall_of_decide (p : α → Prop) [DecidablePred p]
    (h : (all (α := α)).all (fun a => decide (p a)) = true) (a : α) : p a :=
  of_decide_eq_true (forall_of_all (fun a => decide (p a)) h a)

end Universe

end Whatwg.Svg.Data
