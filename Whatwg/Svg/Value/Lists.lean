import Whatwg.Svg.Value.Length

/-!
# Whatwg.Svg.Value.Lists

Owner: the two lists of a text's attributes (slice S8 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-41; debt D96 of ruling R-S19). The authority is the table of attributes under the heading
`TSpanAttributes` of `vendor/w3c-svgwg-47e645ef/master/text.html`, which states them for `text`
and `tspan`:

- `x`, `y`, `dx` and `dy` (`TextElementXAttribute`, `TextElementDXAttribute`) have the value
  `[ [ <length-percentage> | <number> ]+ ]#`: one length or more.
- `rotate` (`TextElementRotateAttribute`) has the value `[ <number>+ ]#`: one number or more.

Both are in the notation of CSS value definitions, where `+` separates by white space and `#`
by a comma. The chapter's prose says of each "a comma- or space-separated list". So the
description is that of `<points>` (`Whatwg/Svg/Value/Points.lean`): `wsp*`, an item, any number
of further items each after `comma_wsp?`, and `wsp*`.

Two typed values:

- `LengthList` is a `Length` and the lengths after it. An item is `Length.item`, the length
  without the white space that `Length.syn` reads around a whole value. Its reading has the
  type of that one, so it has the same value function and no law of its own.
- `NumberList` is a `Decimal` and the numbers after it.

The printer writes the items with one space between. The reader takes a comma, white space,
both, or neither where one item cannot continue into the next: `10px20` is two lengths.

Neither description passes the test of `Whatwg/Svg/Value/Deterministic.lean`, as `<points>`
does not: with no separator, the digits `12` are one number to the reader and two to a
derivation of the bare expression. `WhatwgTest/Svg/Lists.lean` evaluates the test. No text is
known that the expression has and the reader refuses, and none is claimed.

What this module does not claim: what a list means. The chapter gives the n-th value to the
n-th addressable character, and a list that is longer or shorter than the text has a meaning
that no judgment here reads. A unit is one of the ten kinds of `Length` (ruling SV-31).

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- A length with no white space around it: one item of a list. -/
def Length.item : Syn Length :=
  .map Length.ofReading Length.toReading Length.ofReading_toReading
    (.seq sign.opt (.seq fractionalConstant Length.tail))

/-- Every length prints as an item. -/
theorem Length.item_total : Length.item.Total := by
  unfold Length.item
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Length.item_total

/-! ## A list of lengths -/

/-- The typed value of `[ [ <length-percentage> | <number> ]+ ]#`: one length or more, in
order. -/
structure LengthList where
  /-- The first length. -/
  head : Length
  /-- The lengths after it. -/
  tail : List Length
  deriving DecidableEq, Repr, Inhabited

namespace LengthList

/-- The lengths as a list. -/
def toList (l : LengthList) : List Length := l.head :: l.tail

/-- No value is empty: `+` and `#` each ask for one item or more. -/
theorem toList_ne_nil (l : LengthList) : l.toList ≠ [] := List.cons_ne_nil l.head l.tail

/-- The description: `wsp*`, a length, any number of further lengths each after `comma_wsp?`,
and `wsp*`. The lengths print with one space between. -/
def syn : Syn LengthList :=
  .map (fun p => ⟨p.1, p.2⟩) (fun v => (v.head, v.tail)) (fun _ => rfl)
    (.right wsps (.left (Length.item.sepBy1 spaceSep) wsps))

/-- Every value prints: a `LengthList` is made of typed parts. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of a list of lengths. -/
def grammar : Grammar LengthList := ⟨syn, by decide +kernel, syn_total⟩

/-- A list of one length: the place of a text. -/
def single (l : Length) : LengthList := ⟨l, []⟩

/-- A numeral is one length of that many user units: `10 : LengthList`. -/
instance (n : Nat) : OfNat LengthList n := ⟨single (Length.user (.ofInt n))⟩

end LengthList

/-! ## A list of numbers -/

/-- The typed value of `[ <number>+ ]#`: one number or more, in order. -/
structure NumberList where
  /-- The first number. -/
  head : Decimal
  /-- The numbers after it. -/
  tail : List Decimal
  deriving DecidableEq, Repr, Inhabited

namespace NumberList

/-- The numbers as a list. -/
def toList (l : NumberList) : List Decimal := l.head :: l.tail

/-- No value is empty. -/
theorem toList_ne_nil (l : NumberList) : l.toList ≠ [] := List.cons_ne_nil l.head l.tail

/-- The description: `wsp*`, a number, any number of further numbers each after `comma_wsp?`,
and `wsp*`. The numbers print with one space between. -/
def syn : Syn NumberList :=
  .map (fun p => ⟨p.1, p.2⟩) (fun v => (v.head, v.tail)) (fun _ => rfl)
    (.right wsps (.left (Decimal.syn.sepBy1 spaceSep) wsps))

/-- Every value prints: a `NumberList` is made of typed parts. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of a list of numbers. -/
def grammar : Grammar NumberList := ⟨syn, by decide +kernel, syn_total⟩

/-- A list of one number. -/
def single (d : Decimal) : NumberList := ⟨d, []⟩

end NumberList

end Whatwg.Svg.Value
