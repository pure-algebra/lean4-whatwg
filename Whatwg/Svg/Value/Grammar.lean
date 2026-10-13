/-!
# Whatwg.Svg.Value.Grammar

Owner: the one description that reads and prints an attribute value (point T8 of
`docs/SVG-PACKAGE-PLAN.md`, section 3.1; ruling SV-25; slice S4a). Every value grammar of SVG
that this package reads is regular: the number, path data, `points` and `viewBox` nest no
production. So one library serves them all, and each grammar is a value of `Syn`.

This module holds the definitions, and the rules that build a grammar: a carrier imports it to
describe its value. The laws are `Whatwg/Svg/Value/Grammar/Laws.lean`. No carrier reads a law,
so an edit to one rebuilds no carrier (slice S8; debt D98 of ruling R-S21).

A `Syn α` is a typed description of a regular grammar. It is data: `Syn.print` writes a value
as one spelling, and `Syn.read` reads the longest match from the head of a text, with no
backtracking past a choice it has taken. A reader may accept more spellings than the printer
writes: `Syn.skip` reads a part in every spelling and prints its canonical one.

Two facts say when the two agree, and both are computed from the description:

- `Syn.valid g v` says that the value is one the description can print: each character is of
  its set.
- `Syn.ok g` says that one character decides each choice. After a printed part, the first
  character of what follows cannot continue that part; the first alternative of a choice
  cannot start as the second prints; a repeated part ends before its next copy.

A set of characters is a mask over the ASCII code points (ruling SV-22). A character outside
ASCII is in no set, so no description reads one.

`Syn.erase` is the regular expression of a description, and `Regex.Matches` its language.

A `Grammar α` is a description with the two premises: `ok`, and `Syn.Total`, which says that
every value is printable. A description of typed parts is total, and the rules `Syn.Total.seq`,
`Syn.Total.alt` and the others say so, one per form. Each value grammar of this package is one
value of `Grammar`: a carrier discharges `ok` by one evaluation and `Total` by a term of those
rules, which follows its description part by part. A description that holds the parts of
another one reads its totality off the other's.

This module and the carriers ask for no proof search, so a program that imports a grammar
reaches Lean alone. `Whatwg/Svg/Value/Bank.lean` registers the rules in the bank `Whatwg.Syn`,
for a proof that asks for the search.

What this module does not claim: anything of how `read` and `print` agree. That is the
retraction and the soundness of the reader, in `Whatwg/Svg/Value/Grammar/Laws.lean`.
-/

namespace Whatwg.Svg.Value
/-! ## Sets of characters -/

/-- A set of ASCII characters: bit `n` is the character of code point `n`. -/
structure CharSet where
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

namespace CharSet

/-- The empty set. -/
def empty : CharSet := ⟨0⟩

/-- The character is a member. A character outside ASCII is a member of no set. -/
def mem (s : CharSet) (c : Char) : Bool := decide (c.toNat < 128) && s.bits.testBit c.toNat

/-- The set of one character. -/
def single (c : Char) : CharSet := ⟨2 ^ c.toNat⟩

/-- The union. -/
def union (a b : CharSet) : CharSet := ⟨a.bits ||| b.bits⟩

/-- The set of a list's characters. -/
def ofList (cs : List Char) : CharSet := cs.foldl (fun s c => s.union (single c)) empty

/-- The two sets share no member. -/
def disjoint (a b : CharSet) : Bool := a.bits &&& b.bits == 0

theorem mem_empty (c : Char) : empty.mem c = false := by
  simp only [mem, empty, Nat.zero_testBit, Bool.and_false]

theorem mem_union (a b : CharSet) (c : Char) : (a.union b).mem c = (a.mem c || b.mem c) := by
  simp only [mem, union, Nat.testBit_or]
  cases decide (c.toNat < 128) <;> rfl

/-- A member is an ASCII character. -/
theorem lt_of_mem {s : CharSet} {c : Char} (h : s.mem c = true) : c.toNat < 128 := by
  simp only [mem, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem mem_single_self {c : Char} (h : c.toNat < 128) : (single c).mem c = true := by
  simp only [mem, single, Nat.testBit_two_pow, decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨h, trivial⟩

/-- A member of one of two disjoint sets is no member of the other. -/
theorem not_mem_of_disjoint {a b : CharSet} (h : a.disjoint b = true) {c : Char}
    (ha : a.mem c = true) : b.mem c = false := by
  have hzero : a.bits &&& b.bits = 0 := eq_of_beq h
  have hbit : (a.bits &&& b.bits).testBit c.toNat = false := by rw [hzero]; exact Nat.zero_testBit _
  rw [Nat.testBit_and] at hbit
  simp only [mem, Bool.and_eq_true, decide_eq_true_eq] at ha
  rw [ha.2, Bool.true_and] at hbit
  simp only [mem, hbit, Bool.and_false]

/-- The same, read from the other set. -/
theorem not_mem_left_of_disjoint {a b : CharSet} (h : a.disjoint b = true) {c : Char}
    (hb : b.mem c = true) : a.mem c = false := by
  cases ha : a.mem c with
  | false => rfl
  | true =>
    have hnot := not_mem_of_disjoint h ha
    rw [hb] at hnot
    exact Bool.noConfusion hnot

end CharSet

/-- The text does not open with a member of the set: it is empty, or its first character is
no member. -/
def Stops (s : CharSet) (rest : List Char) : Prop :=
  ∀ c t, rest = c :: t → s.mem c = false

theorem Stops.nil (s : CharSet) : Stops s [] := fun _ _ h => nomatch h

theorem Stops.of_union_left {a b : CharSet} {rest : List Char} (h : Stops (a.union b) rest) :
    Stops a rest := fun c t hc => by
  have := h c t hc
  rw [CharSet.mem_union, Bool.or_eq_false_iff] at this
  exact this.1

theorem Stops.of_union_right {a b : CharSet} {rest : List Char} (h : Stops (a.union b) rest) :
    Stops b rest := fun c t hc => by
  have := h c t hc
  rw [CharSet.mem_union, Bool.or_eq_false_iff] at this
  exact this.2

/-! ## The description -/

/-- A typed description of a regular grammar: it reads a value and prints one.

- `eps` is the empty text.
- `one set` is one character of a set.
- `seq a b` is `a`, then `b`.
- `alt a b` is `a`, or else `b`: the reader tries `a` first.
- `many a` is `a` any number of times.
- `map to back h a` is `a` read as another type. `h` says that `to` undoes `back`.
- `skip a canonical` is `a` read in any spelling and forgotten, and printed as `canonical`. -/
inductive Syn : Type → Type 1 where
  | eps : Syn Unit
  | one (set : CharSet) : Syn Char
  | seq {α β : Type} (a : Syn α) (b : Syn β) : Syn (α × β)
  | alt {α β : Type} (a : Syn α) (b : Syn β) : Syn (α ⊕ β)
  | many {α : Type} (a : Syn α) : Syn (List α)
  | map {α β : Type} (to : α → β) (back : β → α) (h : ∀ b, to (back b) = b) (a : Syn α) : Syn β
  | skip {α : Type} (a : Syn α) (canonical : α) : Syn Unit

/-- Read with `step` until it fails or consumes nothing. `fuel` bounds the number of parts. -/
def readMany {α : Type} (step : List Char → Option (α × List Char)) :
    Nat → List Char → List α × List Char
  | 0, s => ([], s)
  | fuel + 1, s =>
    match step s with
    | none => ([], s)
    | some (x, s₁) =>
      if s₁.length < s.length then
        let more := readMany step fuel s₁
        (x :: more.1, more.2)
      else ([], s)

namespace Syn

/-- Write the value: one spelling. -/
def print : {α : Type} → Syn α → α → List Char
  | _, .eps, _ => []
  | _, .one _, c => [c]
  | _, .seq a b, v => a.print v.1 ++ b.print v.2
  | _, .alt a _, .inl x => a.print x
  | _, .alt _ b, .inr y => b.print y
  | _, .many a, xs => xs.flatMap a.print
  | _, .map _ back _ a, v => a.print (back v)
  | _, .skip a canonical, _ => a.print canonical

/-- Read the longest match from the head of the text: the value, and the text that is left. -/
def read : {α : Type} → Syn α → List Char → Option (α × List Char)
  | _, .eps, s => some ((), s)
  | _, .one _, [] => none
  | _, .one set, c :: t => if set.mem c then some (c, t) else none
  | _, .seq a b, s =>
    match a.read s with
    | none => none
    | some (x, s₁) =>
      match b.read s₁ with
      | none => none
      | some (y, s₂) => some ((x, y), s₂)
  | _, .alt a b, s =>
    match a.read s with
    | some (x, s₁) => some (.inl x, s₁)
    | none =>
      match b.read s with
      | some (y, s₁) => some (.inr y, s₁)
      | none => none
  | _, .many a, s => some (readMany a.read s.length s)
  | _, .map to _ _ a, s =>
    match a.read s with
    | none => none
    | some (x, s₁) => some (to x, s₁)
  | _, .skip a _, s =>
    match a.read s with
    | none => none
    | some (_, s₁) => some ((), s₁)

/-- The value is one the description can print: each character is of its set. -/
def valid : {α : Type} → Syn α → α → Bool
  | _, .eps, _ => true
  | _, .one set, c => set.mem c
  | _, .seq a b, v => a.valid v.1 && b.valid v.2
  | _, .alt a _, .inl x => a.valid x
  | _, .alt _ b, .inr y => b.valid y
  | _, .many a, xs => xs.all a.valid
  | _, .map _ back _ a, v => a.valid (back v)
  | _, .skip a canonical, _ => a.valid canonical

/-- A printed value may be the empty text. -/
def printsEmpty : {α : Type} → Syn α → Bool
  | _, .eps => true
  | _, .one _ => false
  | _, .seq a b => a.printsEmpty && b.printsEmpty
  | _, .alt a b => a.printsEmpty || b.printsEmpty
  | _, .many _ => true
  | _, .map _ _ _ a => a.printsEmpty
  | _, .skip a canonical => (a.print canonical).isEmpty

/-- The characters that a printed value may open with. -/
def printFirst : {α : Type} → Syn α → CharSet
  | _, .eps => .empty
  | _, .one set => set
  | _, .seq a b => if a.printsEmpty then a.printFirst.union b.printFirst else a.printFirst
  | _, .alt a b => a.printFirst.union b.printFirst
  | _, .many a => a.printFirst
  | _, .map _ _ _ a => a.printFirst
  | _, .skip a canonical =>
    match a.print canonical with
    | [] => .empty
    | c :: _ => .single c

/-- The reader may succeed and consume nothing. -/
def readsEmpty : {α : Type} → Syn α → Bool
  | _, .eps => true
  | _, .one _ => false
  | _, .seq a b => a.readsEmpty && b.readsEmpty
  | _, .alt a b => a.readsEmpty || b.readsEmpty
  | _, .many _ => true
  | _, .map _ _ _ a => a.readsEmpty
  | _, .skip a _ => a.readsEmpty

/-- The characters that a text the reader consumes may open with. -/
def readFirst : {α : Type} → Syn α → CharSet
  | _, .eps => .empty
  | _, .one set => set
  | _, .seq a b => if a.readsEmpty then a.readFirst.union b.readFirst else a.readFirst
  | _, .alt a b => a.readFirst.union b.readFirst
  | _, .many a => a.readFirst
  | _, .map _ _ _ a => a.readFirst
  | _, .skip a _ => a.readFirst

/-- The characters that may continue the reader past a printed value: a text that opens with
none of them leaves the reader where the print ends. -/
def continues : {α : Type} → Syn α → CharSet
  | _, .eps => .empty
  | _, .one _ => .empty
  | _, .seq a b => if b.printsEmpty then b.continues.union a.continues else b.continues
  | _, .alt a b =>
    if b.printsEmpty then (a.continues.union b.continues).union a.readFirst
    else a.continues.union b.continues
  | _, .many a => a.continues.union a.readFirst
  | _, .map _ _ _ a => a.continues
  | _, .skip a _ => a.continues

/-- One character decides each choice of the reader on a printed value. -/
def ok : {α : Type} → Syn α → Bool
  | _, .eps => true
  | _, .one _ => true
  | _, .seq a b => a.ok && b.ok && a.continues.disjoint b.printFirst
  | _, .alt a b => a.ok && b.ok && !a.readsEmpty && a.readFirst.disjoint b.printFirst
  | _, .many a => a.ok && !a.readsEmpty && !a.printsEmpty && a.continues.disjoint a.printFirst
  | _, .map _ _ _ a => a.ok
  | _, .skip a canonical => a.ok && a.valid canonical

/-! ## A whole text -/

/-- The value of a whole text: the reader's answer when nothing is left. -/
def readAll {α : Type} (g : Syn α) (s : List Char) : Option α :=
  match g.read s with
  | some (v, []) => some v
  | _ => none

/-- The text is a spelling the description reads in full. -/
def check {α : Type} (g : Syn α) (s : List Char) : Bool := (g.readAll s).isSome

end Syn

/-! ## The regular expression of a description -/

/-- A regular expression over sets of characters: what a description erases to. -/
inductive Regex where
  | eps
  | set (s : CharSet)
  | seq (a b : Regex)
  | alt (a b : Regex)
  | star (a : Regex)
  deriving Repr, Inhabited

/-- The language of an expression: the texts it matches. -/
inductive Regex.Matches : Regex → List Char → Prop where
  | eps : Matches .eps []
  | set {s : CharSet} {c : Char} : s.mem c = true → Matches (.set s) [c]
  | seq {a b : Regex} {l₁ l₂ : List Char} : Matches a l₁ → Matches b l₂ →
      Matches (.seq a b) (l₁ ++ l₂)
  | altL {a b : Regex} {l : List Char} : Matches a l → Matches (.alt a b) l
  | altR {a b : Regex} {l : List Char} : Matches b l → Matches (.alt a b) l
  | starNil {a : Regex} : Matches (.star a) []
  | starCons {a : Regex} {l₁ l₂ : List Char} : Matches a l₁ → Matches (.star a) l₂ →
      Matches (.star a) (l₁ ++ l₂)

namespace Syn

/-- The regular expression of a description: its shape without the types. -/
def erase : {α : Type} → Syn α → Regex
  | _, .eps => .eps
  | _, .one s => .set s
  | _, .seq a b => .seq a.erase b.erase
  | _, .alt a b => .alt a.erase b.erase
  | _, .many a => .star a.erase
  | _, .map _ _ _ a => a.erase
  | _, .skip a _ => a.erase

/-! ## Derived descriptions -/

/-- `a`, or nothing. The reader tries `a` first. -/
def opt {α : Type} (a : Syn α) : Syn (Option α) :=
  .map (fun v => match v with | .inl x => some x | .inr _ => none)
    (fun v => match v with | some x => .inl x | none => .inr ())
    (fun b => by cases b <;> rfl) (.alt a .eps)

/-- `a`, once or more: the first value and the ones after it. -/
def many1 {α : Type} (a : Syn α) : Syn (α × List α) := .seq a (.many a)

/-- `a`, then a part with nothing to keep. -/
def left {α : Type} (a : Syn α) (b : Syn Unit) : Syn α :=
  .map (fun p => p.1) (fun x => (x, ())) (fun _ => rfl) (.seq a b)

/-- A part with nothing to keep, then `b`. -/
def right {β : Type} (a : Syn Unit) (b : Syn β) : Syn β :=
  .map (fun p => p.2) (fun y => ((), y)) (fun _ => rfl) (.seq a b)

/-- `a (sep a)*`: `a` once or more, with `sep` before each one after the first. The value is
the first `a` and the ones after it. -/
def sepBy1 {α : Type} (a : Syn α) (sep : Syn Unit) : Syn (α × List α) :=
  .seq a (.many (.right sep a))

/-- The exact text. -/
def lit : List Char → Syn Unit
  | [] => .eps
  | c :: cs => .right (.skip (.one (.single c)) c) (lit cs)

/-! ## Descriptions that print every value -/

/-- Every value is one the description can print. A description of typed parts is total: its
characters are chosen by `back`, never by the caller. -/
def Total {α : Type} (g : Syn α) : Prop := ∀ v, g.valid v = true

theorem Total.eps : Syn.eps.Total := fun _ => rfl

theorem Total.seq {α β : Type} {a : Syn α} {b : Syn β} (ha : a.Total) (hb : b.Total) :
    (Syn.seq a b).Total := fun v => by
  simp only [valid, ha v.1, hb v.2, Bool.and_self]

theorem Total.alt {α β : Type} {a : Syn α} {b : Syn β} (ha : a.Total) (hb : b.Total) :
    (Syn.alt a b).Total := fun v => by
  cases v with
  | inl x => exact ha x
  | inr y => exact hb y

theorem Total.many {α : Type} {a : Syn α} (ha : a.Total) : (Syn.many a).Total := fun xs => by
  simp only [valid]
  exact List.all_eq_true.mpr fun x _ => ha x

theorem Total.map {α β : Type} {to : α → β} {back : β → α} {h : ∀ b, to (back b) = b}
    {a : Syn α} (ha : a.Total) : (Syn.map to back h a).Total := fun v => ha (back v)

/-- A part read in any spelling prints every value, when its canonical spelling is printable:
a description of `Unit` has one value. -/
theorem Total.of_unit {g : Syn Unit} (h : g.valid () = true) : g.Total := fun _ => h

theorem Total.opt {α : Type} {a : Syn α} (ha : a.Total) : a.opt.Total :=
  Total.map (Total.alt ha Total.eps)

theorem Total.many1 {α : Type} {a : Syn α} (ha : a.Total) : a.many1.Total :=
  Total.seq ha (Total.many ha)

theorem Total.left {α : Type} {a : Syn α} {b : Syn Unit} (ha : a.Total) (hb : b.Total) :
    (a.left b).Total := Total.map (Total.seq ha hb)

theorem Total.right {β : Type} {a : Syn Unit} {b : Syn β} (ha : a.Total) (hb : b.Total) :
    (a.right b).Total := Total.map (Total.seq ha hb)

theorem Total.sepBy1 {α : Type} {a : Syn α} {sep : Syn Unit} (ha : a.Total) (hsep : sep.Total) :
    (a.sepBy1 sep).Total := Total.seq ha (Total.many (Total.right hsep ha))

end Syn

/-! ## A grammar -/

/-- A description with the two premises of its laws: one character decides each choice, and
every value prints. A value grammar of this package is one value of this type, and its reader,
its printer and its laws are the ones below. -/
structure Grammar (α : Type) where
  /-- The description. -/
  syn : Syn α
  /-- One character decides each choice: one evaluation. -/
  ok : syn.ok = true
  /-- Every value prints. -/
  total : syn.Total

namespace Grammar

variable {α : Type}

/-- Write the value: one spelling. -/
def print (g : Grammar α) (v : α) : List Char := g.syn.print v

/-- The value of a whole text, in any spelling the description reads. -/
def read (g : Grammar α) (s : List Char) : Option α := g.syn.readAll s

/-- The text is a spelling of some value. -/
def check (g : Grammar α) (s : List Char) : Bool := g.syn.check s

theorem check_eq (g : Grammar α) (s : List Char) : g.check s = (g.read s).isSome := rfl

end Grammar

end Whatwg.Svg.Value
