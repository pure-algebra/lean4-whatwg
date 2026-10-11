import Whatwg.Svg.Data.Universe

/-!
# Whatwg.Svg.Data.NameTable

A name table: an exact embedding of a universe into spellings (point T6 of
`docs/SVG-PACKAGE-PLAN.md`, section 3.1; ruling SV-24). The writer is `chars`. The reader is
`read`, built once for every table: it takes a guess of the value that a spelling names, and
keeps the guess only if the guess spells the input.

So the generated decision tree is a guess and no more. The exactness, `read_exact`, holds by
construction for any guess. The retraction, `read_chars`, needs one premise per table: the
guess finds every value from its own spelling. `covers` is that premise as a Boolean over the
census, and one `decide` discharges it (node N1 of the plan's section 6). No proof splits over
a generated match.

Names are compared exactly, as lists of characters. This module reads no `String`.
-/

namespace Whatwg.Svg.Data

/-- A name table: each value's spelling, and a guess of the value that a spelling names. -/
structure NameTable (α : Type) where
  /-- The spelling of a value. -/
  chars : α → List Char
  /-- A value that the spelling may name. `read` checks it. -/
  guess : List Char → Option α

namespace NameTable

variable {α : Type}

/-- The value that a spelling names: the guess, kept only if it spells the input. -/
def read (n : NameTable α) (s : List Char) : Option α :=
  match n.guess s with
  | some a => if n.chars a = s then some a else none
  | none => none

/-- Exactness: a spelling that reads as a value is that value's spelling. -/
theorem read_exact {n : NameTable α} {s : List Char} {a : α} (h : n.read s = some a) :
    n.chars a = s := by
  unfold read at h
  split at h
  · split at h
    · next hb => exact Option.some.inj h ▸ hb
    · exact nomatch h
  · exact nomatch h

/-- The retraction: a value's spelling reads back as the value, when the guess finds it. -/
theorem read_chars {n : NameTable α} (hg : ∀ a, n.guess (n.chars a) = some a) (a : α) :
    n.read (n.chars a) = some a := by
  unfold read
  rw [hg a]
  exact if_pos rfl

/-- With the retraction, the spelling is injective. -/
theorem chars_injective {n : NameTable α} (hg : ∀ a, n.guess (n.chars a) = some a) {a b : α}
    (h : n.chars a = n.chars b) : a = b := by
  have ha := read_chars hg a
  rw [h, read_chars hg b] at ha
  exact (Option.some.inj ha).symm

/-- With the retraction, `read` answers a value exactly on that value's spelling. -/
theorem read_eq_some_iff {n : NameTable α} (hg : ∀ a, n.guess (n.chars a) = some a)
    {s : List Char} {a : α} : n.read s = some a ↔ n.chars a = s :=
  ⟨read_exact, fun h => h ▸ read_chars hg a⟩

variable [Universe α] [DecidableEq α]

/-- The premise of the retraction as a Boolean over the census: the guess finds every value
from its own spelling. -/
def covers (n : NameTable α) : Bool :=
  (Universe.all (α := α)).all fun a => decide (n.guess (n.chars a) = some a)

/-- The premise of the retraction, from its Boolean. -/
theorem guess_chars {n : NameTable α} (h : n.covers = true) (a : α) :
    n.guess (n.chars a) = some a :=
  Universe.forall_of_decide (fun a => n.guess (n.chars a) = some a) h a

end NameTable

end Whatwg.Svg.Data
