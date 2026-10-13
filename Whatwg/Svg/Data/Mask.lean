import Whatwg.Svg.Data.Universe

/-!
# Whatwg.Svg.Data.Mask

A set over a finite universe, as a `Nat` whose bit `i` is the value of index `i` (point T4 of
`docs/SVG-PACKAGE-PLAN.md`, section 3.1; ruling SV-22). Union is `|||`, intersection is `&&&`,
and membership is `Nat.testBit`. The kernel evaluates these `Nat` operations natively, so one
definition is the specification and the fast test.

`mem` is a homomorphism into `Bool` (node B1 of the plan's section 6): `mem_union`, `mem_inter`,
`mem_diff`, `mem_single` and `mem_ofList` say what each operation does to membership. The first
two are each one core lemma about `Nat.testBit`; `mem_single` also needs that the index is
injective, and `mem_ofList` an induction on the list.

What this module does not claim: that two masks with the same members are equal. A bit above
the universe's length names no value, so `mem` does not see it. The generator writes no such
bit, and no law here needs extensionality.

This module asks for no proof search, so a program that imports it reaches Lean alone. The
rules of the bank `Whatwg.Mask` are `Whatwg/Svg/Data/Mask/Laws.lean`.
-/

namespace Whatwg.Svg.Data

/-- A set of values of a universe: bit `i` is set when the value of index `i` is a member. -/
structure Mask (α : Type) where
  bits : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Mask

variable {α : Type}

/-- The empty set. -/
def empty : Mask α := ⟨0⟩

/-- The union. -/
def union (m n : Mask α) : Mask α := ⟨m.bits ||| n.bits⟩

/-- The intersection. -/
def inter (m n : Mask α) : Mask α := ⟨m.bits &&& n.bits⟩

/-- The members of `m` that `n` does not hold. -/
def diff (m n : Mask α) : Mask α := ⟨m.bits ^^^ (m.bits &&& n.bits)⟩

/-- Every member of `m` is a member of `n`. -/
def subset (m n : Mask α) : Bool := m.bits &&& n.bits == m.bits

variable [Universe α]

/-- The value is a member. -/
def mem (m : Mask α) (a : α) : Bool := m.bits.testBit (Universe.index a)

/-- The set of one value. -/
def single (a : α) : Mask α := ⟨2 ^ Universe.index a⟩

/-- The set with one more value. -/
def insert (m : Mask α) (a : α) : Mask α := m.union (single a)

/-- The set of a list's values. -/
def ofList (l : List α) : Mask α := l.foldl insert empty

/-- The members, in index order. -/
def toList (m : Mask α) : List α := (Universe.all (α := α)).filter m.mem

/-- How many values of the list are members. -/
def count (m : Mask α) (l : List α) : Nat := l.countP m.mem

/-! ## Membership is a homomorphism -/

theorem mem_empty (a : α) : (empty : Mask α).mem a = false := Nat.zero_testBit _

theorem mem_union (m n : Mask α) (a : α) : (m.union n).mem a = (m.mem a || n.mem a) :=
  Nat.testBit_or _ _ _

theorem mem_inter (m n : Mask α) (a : α) : (m.inter n).mem a = (m.mem a && n.mem a) :=
  Nat.testBit_and _ _ _

theorem mem_diff (m n : Mask α) (a : α) : (m.diff n).mem a = (m.mem a && !n.mem a) := by
  simp only [mem, diff, Nat.testBit_xor, Nat.testBit_and]
  cases m.bits.testBit (Universe.index a) <;> cases n.bits.testBit (Universe.index a) <;> rfl

theorem mem_single (a b : α) : (single a).mem b = true ↔ a = b := by
  simp only [mem, single, Nat.testBit_two_pow, decide_eq_true_eq]
  exact ⟨Universe.index_injective, fun h => h ▸ rfl⟩

theorem mem_insert (m : Mask α) (a b : α) : (m.insert a).mem b = true ↔ m.mem b = true ∨ a = b := by
  simp only [insert, mem_union, Bool.or_eq_true, mem_single]

theorem mem_foldl_insert (l : List α) (m : Mask α) (a : α) :
    (l.foldl insert m).mem a = true ↔ m.mem a = true ∨ a ∈ l := by
  induction l generalizing m with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, or_false]
  | cons b rest ih =>
    simp only [List.foldl_cons, ih, mem_insert, List.mem_cons]
    constructor
    · intro h
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · intro h
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

/-- A mask built from a list holds exactly the list's values. -/
theorem mem_ofList (l : List α) (a : α) : (ofList l).mem a = true ↔ a ∈ l := by
  simp only [ofList, mem_foldl_insert, mem_empty, Bool.false_eq_true, false_or]

theorem mem_toList (m : Mask α) (a : α) : a ∈ m.toList ↔ m.mem a = true := by
  simp only [toList, List.mem_filter, Universe.mem_all, true_and]

/-- A member of a subset is a member of the larger set. -/
theorem mem_of_subset {m n : Mask α} (h : m.subset n = true) {a : α} (ha : m.mem a = true) :
    n.mem a = true := by
  have hbits : m.bits &&& n.bits = m.bits := eq_of_beq h
  have hand : (m.bits &&& n.bits).testBit (Universe.index a) = true := by rw [hbits]; exact ha
  rw [Nat.testBit_and, Bool.and_eq_true] at hand
  exact hand.2

end Mask

end Whatwg.Svg.Data
