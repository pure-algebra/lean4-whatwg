import Whatwg.Svg.Value.Grammar

/-!
# Whatwg.Svg.Value.Number

Owner: the number of an SVG attribute value, and the separators between numbers (slice S4b of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-26). The authority is the grammar under the heading
`PathDataBNF` of `vendor/w3c-svgwg-47e645ef/master/paths.html`: the productions `digit`, `wsp`,
`comma_wsp`, `sign`, `exponent`, `fractional-constant`, `number` and `coordinate`.

Three typed values:

- `Magnitude` is the production `number`: an unsigned exact decimal, `mantissa × 10 ^ exponent`.
- `Decimal` is the production `coordinate`, `sign? number`: a signed exact decimal.
- `Point` is the production `coordinate_pair`: two decimals.

Neither number is a floating-point number, and nothing here rounds. A conversion from a
rational is a rounding, so it is the caller's. This module offers the exact ones:
`Decimal.ofInt`, `Decimal.ofScaled`, `Magnitude.ofNat`, and `Magnitude.ofInt?`, which refuses a
negative integer.

Each is a `Grammar`, so its laws are those of `Whatwg/Svg/Value/Grammar.lean`. The printer
writes one spelling of a value:

- exponent zero: the digits of the mantissa, `150`;
- a positive exponent: the digits and the exponent, `15e1`;
- a negative exponent: the digits with a point, and a zero before a bare fraction, `1.50` and
  `0.025`; or the digits and the exponent where that is shorter, `5e-3`.

The value is the pair, not the number it denotes: `150` and `15e1` are two values, and the
reader tells them apart. The reader takes every spelling of the grammar: `+.5E-2` reads as
`5 × 10 ^ -3`. A reading keeps the digits it is given, so the cost of a read is the length of
the text, whatever exponent the text states. The cost of a print is the length of its text
too: the printer takes no power of ten that the spelling does not write.

Two productions are described with one reading each, and the language is the same:

- `comma_wsp` is `(wsp+ ","? wsp*) | ("," wsp*)`. A run of white space with no comma is one
  run, so the description is `(wsp+ ("," wsp*)?) | ("," wsp*)`.
- `fractional-constant` is `(digit* "." digit+) | digit+`. The description is
  `(digit+ ("." digit+)?) | ("." digit+)`.

There are two exact layers, and each has its name:

- A text and a value: the spelling layer. The reader takes many spellings and the printer
  writes one, so the two are exact up to the printer's choice.
- A value and its number: the denotation layer, which is `Whatwg/Svg/Value/Cohort.lean`. The
  values of one number are its cohort. `Decimal.Same` states that two values denote one
  number, `Decimal.reduce` gives the cohort's canonical value, and `Decimal.tidy` writes it
  plain where that is no longer.

`Decimal.trim` is here, because a program builds values with it: the value of the same number
with no zero at the end of its fraction. A count in thousandths is `(ofScaled n 3).trim`, and
it prints as `10`, `13.288` and `15000`.

What this module does not claim: that two values which denote one number are equal, or that
the reader returns a canonical value (`1.50` reads as `150 × 10 ^ -2`).

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-! ## The characters -/

/-- `digit`. -/
def digitSet : CharSet := .ofList ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

/-- `wsp`: tab, space, line feed, form feed and carriage return. -/
def wspSet : CharSet := .ofList ['\t', ' ', '\n', '\x0c', '\r']

/-- `sign`. -/
def signSet : CharSet := .ofList ['+', '-']

/-- The mark of an exponent. -/
def exponentSet : CharSet := .ofList ['e', 'E']

/-! ## The separators

Each takes the set of white space. Path data, `points` and `viewBox` use `wspSet`; the
`transform` grammar of CSS Transforms 1 states a set of its own. -/

/-- `wsp*`, read in any amount and printed as nothing. -/
def wspsOf (ws : CharSet) : Syn Unit := .skip (.many (.one ws)) []

/-- The spellings of `comma_wsp`: white space and then at most one comma, or a comma, each
comma with white space after it. -/
def commaWspSpellings (ws : CharSet) :
    Syn (((Char × List Char) × Option (Char × List Char)) ⊕ (Char × List Char)) :=
  .alt (.seq (Syn.one ws).many1 (Syn.seq (.one (.single ',')) (.many (.one ws))).opt)
    (.seq (.one (.single ',')) (.many (.one ws)))

/-- `comma_wsp`, printed as one space. -/
def commaWspOf (ws : CharSet) : Syn Unit := .skip (commaWspSpellings ws) (.inl ((' ', []), none))

/-- `comma_wsp?`, printed as one space. -/
def spaceSepOf (ws : CharSet) : Syn Unit :=
  .skip (commaWspSpellings ws).opt (some (.inl ((' ', []), none)))

/-- `comma_wsp?`, printed as a comma. -/
def commaSepOf (ws : CharSet) : Syn Unit :=
  .skip (commaWspSpellings ws).opt (some (.inr (',', [])))

/-- `wsp*` of path data. -/
def wsps : Syn Unit := wspsOf wspSet

/-- `comma_wsp` of path data, printed as one space. -/
def commaWsp : Syn Unit := commaWspOf wspSet

/-- `comma_wsp?` of path data, printed as one space. -/
def spaceSep : Syn Unit := spaceSepOf wspSet

/-- `comma_wsp?` of path data, printed as a comma. -/
def commaSep : Syn Unit := commaSepOf wspSet

theorem wsps_total : wsps.Total := Syn.Total.of_unit (by decide)
theorem commaWsp_total : commaWsp.Total := Syn.Total.of_unit (by decide)
theorem spaceSep_total : spaceSep.Total := Syn.Total.of_unit (by decide)
theorem commaSep_total : commaSep.Total := Syn.Total.of_unit (by decide)

/-- The exact text prints, when each character is ASCII: one evaluation. -/
theorem lit_total (cs : List Char) (h : (Syn.lit cs).valid () = true) : (Syn.lit cs).Total :=
  Syn.Total.of_unit h

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])]
  wsps_total commaWsp_total spaceSep_total commaSep_total lit_total

/-! ## Digits -/

/-- One digit, as its value. -/
def digit : Syn (Fin 10) :=
  .map (fun c => ⟨(c.toNat - 48) % 10, Nat.mod_lt _ (by decide)⟩)
    (fun d => Char.ofNat (48 + d.val)) (by decide) (.one digitSet)

theorem digit_total : digit.Total := fun d => by
  revert d
  decide

/-- The number a digit list writes, most significant digit first. -/
def digitsValue (ds : List (Fin 10)) : Nat := ds.foldl (fun n d => n * 10 + d.val) 0

/-- The last `width` digits of `n`, most significant first, with leading zeros. -/
def fixedDigits : Nat → Nat → List (Fin 10)
  | 0, _ => []
  | width + 1, n => fixedDigits width (n / 10) ++ [⟨n % 10, Nat.mod_lt _ (by decide)⟩]

/-- The digits of `n` with no leading zero. `fuel` bounds their number. -/
def natDigitsAux : Nat → Nat → List (Fin 10)
  | 0, _ => []
  | fuel + 1, n =>
    (if n < 10 then [] else natDigitsAux fuel (n / 10)) ++ [⟨n % 10, Nat.mod_lt _ (by decide)⟩]

/-- The digits of `n` with no leading zero. Zero is one digit. -/
def natDigits (n : Nat) : List (Fin 10) := natDigitsAux (n + 1) n

/-- A digit list as its first digit and the rest. The empty list is one zero. -/
def headTail (ds : List (Fin 10)) : Fin 10 × List (Fin 10) :=
  match ds with
  | [] => (0, [])
  | d :: t => (d, t)

theorem foldl_digit (ds : List (Fin 10)) (acc : Nat) :
    ds.foldl (fun n d => n * 10 + d.val) acc =
      acc * 10 ^ ds.length + ds.foldl (fun n d => n * 10 + d.val) 0 := by
  induction ds generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | cons d t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (acc * 10 + d.val), ih (0 * 10 + d.val), Nat.pow_succ, Nat.zero_mul, Nat.zero_add,
      Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10, Nat.add_assoc]

theorem digitsValue_append (a b : List (Fin 10)) :
    digitsValue (a ++ b) = digitsValue a * 10 ^ b.length + digitsValue b := by
  simp only [digitsValue, List.foldl_append]
  exact foldl_digit b _

theorem digitsValue_snoc (a : List (Fin 10)) (d : Fin 10) :
    digitsValue (a ++ [d]) = digitsValue a * 10 + d.val := by
  simp only [digitsValue, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem length_fixedDigits : ∀ width n : Nat, (fixedDigits width n).length = width
  | 0, _ => rfl
  | width + 1, n => by
    simp only [fixedDigits, List.length_append, length_fixedDigits width (n / 10),
      List.length_cons, List.length_nil, Nat.zero_add]

/-- Fixed-width digits write what the quotient by the width's power of ten leaves: the two
parts of a number at a decimal point make the number. -/
theorem div_mul_add_fixedDigits : ∀ width n : Nat,
    n / 10 ^ width * 10 ^ width + digitsValue (fixedDigits width n) = n
  | 0, n => by
    simp only [fixedDigits, digitsValue, List.foldl_nil, Nat.pow_zero, Nat.div_one, Nat.mul_one,
      Nat.add_zero]
  | width + 1, n => by
    have ih := div_mul_add_fixedDigits width (n / 10)
    rw [fixedDigits, digitsValue_snoc, Nat.pow_succ, Nat.mul_comm (10 ^ width) 10,
      ← Nat.div_div_eq_div_mul, Nat.mul_left_comm]
    show 10 * (n / 10 / 10 ^ width * 10 ^ width) +
      (digitsValue (fixedDigits width (n / 10)) * 10 + n % 10) = n
    generalize n / 10 / 10 ^ width * 10 ^ width = high at ih ⊢
    generalize digitsValue (fixedDigits width (n / 10)) = low at ih ⊢
    omega

theorem digitsValue_natDigitsAux : ∀ fuel n : Nat, n < fuel →
    digitsValue (natDigitsAux fuel n) = n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, h => by
    rw [natDigitsAux, digitsValue_snoc]
    show digitsValue (if n < 10 then [] else natDigitsAux fuel (n / 10)) * 10 + n % 10 = n
    cases hlt : decide (n < 10) with
    | true =>
      have hlt' : n < 10 := of_decide_eq_true hlt
      rw [if_pos hlt']
      show 0 * 10 + n % 10 = n
      omega
    | false =>
      have hge : ¬ n < 10 := of_decide_eq_false hlt
      rw [if_neg hge, digitsValue_natDigitsAux fuel (n / 10) (by omega)]
      omega

/-- The digits of a number write that number. -/
theorem digitsValue_natDigits (n : Nat) : digitsValue (natDigits n) = n :=
  digitsValue_natDigitsAux (n + 1) n (Nat.lt_succ_self n)

theorem digitsValue_headTail (ds : List (Fin 10)) :
    digitsValue ((headTail ds).1 :: (headTail ds).2) = digitsValue ds := by
  cases ds with
  | nil => rfl
  | cons d t => rfl

theorem headTail_cons {ds : List (Fin 10)} {width : Nat} (h : ds.length = width + 1) :
    (headTail ds).1 :: (headTail ds).2 = ds := by
  cases ds with
  | nil => exact nomatch h
  | cons d t => rfl

/-- `digit+` as a natural number, printed with no leading zero. -/
def natural : Syn Nat :=
  .map (fun p => digitsValue (p.1 :: p.2)) (fun n => headTail (natDigits n))
    (fun n => by rw [digitsValue_headTail, digitsValue_natDigits]) digit.many1

theorem natural_total : natural.Total := Syn.Total.map (Syn.Total.many1 digit_total)

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] digit_total natural_total

/-! ## The unsigned number -/

/-- An unsigned exact decimal, `mantissa × 10 ^ exponent`: the typed value of the production
`number`. -/
structure Magnitude where
  mantissa : Nat
  exponent : Int
  deriving DecidableEq, Repr, Inhabited

/-- A sign: `true` is `-`. -/
def sign : Syn Bool :=
  .map (fun c => c == '-') (fun b => if b then '-' else '+') (by decide) (.one signSet)

theorem sign_total : sign.Total := fun b => by
  revert b
  decide

/-- `"+"?`, read and printed as nothing: the sign of a number that must not be negative. No
production of the path data grammar is such a number, so a grammar that needs one reads this
and then `number`. A minus sign is refused, before a zero too. -/
def plus : Syn Unit := .skip (Syn.one (.single '+')).opt none

/-- The one value of `plus` prints: its canonical reading is no sign. -/
theorem plus_total : plus.Total := Syn.Total.of_unit (by decide)

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] plus_total

/-- `"." digit+`. A part with no type of its own is an `abbrev`: the search that proves a
grammar total (`Whatwg.Syn`) reads through it, so a part states no totality lemma. -/
abbrev fraction : Syn (Fin 10 × List (Fin 10)) := .right (.lit ['.']) digit.many1

/-- `fractional-constant`: digits with or without a fraction, or a fraction alone. -/
abbrev fractionalConstant :
    Syn (((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) :=
  .alt (.seq digit.many1 fraction.opt) fraction

/-- `exponent?`. The mark is read as `e` or `E` and printed as `e`. -/
def exponentPart : Syn (Option (Option Bool × Nat)) :=
  (Syn.right (.skip (.one exponentSet) 'e') (.seq sign.opt natural)).opt

theorem exponentPart_total : exponentPart.Total :=
  Syn.Total.opt (Syn.Total.right (Syn.Total.of_unit (by decide))
    (Syn.Total.seq (Syn.Total.opt sign_total) natural_total))

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] sign_total exponentPart_total

/-- The exponent that a reading states. No exponent is zero. -/
def exponentValue : Option (Option Bool × Nat) → Int
  | none => 0
  | some (some true, n) => -(n : Int)
  | some (_, n) => n

namespace Magnitude

/-- The value of a reading: the digits as one number, and the stated exponent less the number
of digits after the point. -/
def ofReading
    (r : (((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) × Option (Option Bool × Nat)) : Magnitude :=
  match r.1 with
  | .inl (i, none) => ⟨digitsValue (i.1 :: i.2), exponentValue r.2⟩
  | .inl (i, some f) =>
    ⟨digitsValue ((i.1 :: i.2) ++ (f.1 :: f.2)), exponentValue r.2 - ((f.2.length + 1 : Nat) : Int)⟩
  | .inr f => ⟨digitsValue (f.1 :: f.2), exponentValue r.2 - ((f.2.length + 1 : Nat) : Int)⟩

/-- A fraction of `places` digits is written with a point: that spelling is no longer than the
one with an exponent. With fewer digits than places, the point costs `places + 2` characters
and the exponent costs the digits, the mark, the sign and the digits of `places`. -/
def pointed (mantissa places : Nat) : Bool :=
  decide (places ≤ (natDigits mantissa).length + (natDigits places).length)

/-- The one spelling of a value: plain digits at exponent zero, an exponent at a positive one,
and at a negative one the shorter of a point and an exponent. The cost is the length of the
spelling: no power of ten is taken that the spelling does not write. -/
def toReading (u : Magnitude) :
    (((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) × Option (Option Bool × Nat) :=
  match u.exponent with
  | .ofNat 0 => (.inl (headTail (natDigits u.mantissa), none), none)
  | .ofNat (k + 1) => (.inl (headTail (natDigits u.mantissa), none), some (none, k + 1))
  | .negSucc k =>
    if pointed u.mantissa (k + 1) then
      (.inl (headTail (natDigits (u.mantissa / 10 ^ (k + 1))),
        some (headTail (fixedDigits (k + 1) u.mantissa))), none)
    else (.inl (headTail (natDigits u.mantissa), none), some (some true, k + 1))

/-- A value's spelling reads as the value. -/
theorem ofReading_toReading (u : Magnitude) : ofReading (toReading u) = u := by
  cases u with
  | mk m e =>
    cases e with
    | ofNat n =>
      cases n with
      | zero =>
        show Magnitude.mk (digitsValue ((headTail (natDigits m)).1 :: (headTail (natDigits m)).2))
          0 = _
        rw [digitsValue_headTail, digitsValue_natDigits]
        rfl
      | succ k =>
        show Magnitude.mk (digitsValue ((headTail (natDigits m)).1 :: (headTail (natDigits m)).2))
          ((k + 1 : Nat) : Int) = _
        rw [digitsValue_headTail, digitsValue_natDigits]
        rfl
    | negSucc k =>
      show ofReading (if pointed m (k + 1) = true then _ else _) = _
      cases hp : pointed m (k + 1) with
      | true =>
        have hfix := headTail_cons (length_fixedDigits (k + 1) m)
        have hlen : (headTail (fixedDigits (k + 1) m)).2.length + 1 = k + 1 := by
          have h := congrArg List.length hfix
          rw [List.length_cons, length_fixedDigits] at h
          exact h
        rw [if_pos rfl]
        show Magnitude.mk
          (digitsValue (((headTail (natDigits (m / 10 ^ (k + 1)))).1 ::
            (headTail (natDigits (m / 10 ^ (k + 1)))).2) ++
            ((headTail (fixedDigits (k + 1) m)).1 :: (headTail (fixedDigits (k + 1) m)).2)))
          (0 - (((headTail (fixedDigits (k + 1) m)).2.length + 1 : Nat) : Int)) = _
        rw [hfix, hlen, digitsValue_append, digitsValue_headTail, digitsValue_natDigits,
          length_fixedDigits, div_mul_add_fixedDigits]
        rfl
      | false =>
        rw [if_neg Bool.false_ne_true]
        show Magnitude.mk (digitsValue ((headTail (natDigits m)).1 :: (headTail (natDigits m)).2))
          (-((k + 1 : Nat) : Int)) = _
        rw [digitsValue_headTail, digitsValue_natDigits]
        rfl

/-- The description of `number`. -/
def syn : Syn Magnitude :=
  .map ofReading toReading ofReading_toReading (.seq fractionalConstant exponentPart)

theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `number`. -/
def grammar : Grammar Magnitude := ⟨syn, by decide +kernel, syn_total⟩

/-- A natural number, exactly. -/
def ofNat (n : Nat) : Magnitude := ⟨n, 0⟩

/-- A numeral is the natural number it writes: `320 : Magnitude`. -/
instance (n : Nat) : OfNat Magnitude n := ⟨ofNat n⟩

/-- An integer that is not negative, exactly. A negative one is no value: a size that a
program computes as a difference is refused here, and never clamped. -/
def ofInt? : Int → Option Magnitude
  | .ofNat n => some (ofNat n)
  | .negSucc _ => none

theorem ofInt?_natCast (n : Nat) : ofInt? (n : Int) = some (ofNat n) := rfl

theorem ofInt?_of_nonneg {v : Int} (h : 0 ≤ v) : ofInt? v = some (ofNat v.toNat) := by
  cases v with
  | ofNat n => rfl
  | negSucc n => exact absurd h (Int.not_le.mpr (Int.negSucc_lt_zero n))

theorem ofInt?_of_neg {v : Int} (h : v < 0) : ofInt? v = none := by
  cases v with
  | ofNat n => exact absurd h (Int.not_lt.mpr (Int.natCast_nonneg n))
  | negSucc n => rfl

end Magnitude

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Magnitude.syn_total

/-! ## The signed number -/

/-- A signed exact decimal, `mantissa × 10 ^ exponent`: the typed value of the production
`coordinate`, and of `<number>` in an attribute value. -/
structure Decimal where
  mantissa : Int
  exponent : Int
  deriving DecidableEq, Repr, Inhabited

namespace Decimal

/-- The value of a sign and a magnitude. `+` and no sign are one value. -/
def ofReading (r : Option Bool × Magnitude) : Decimal :=
  match r.1 with
  | some true => ⟨-(r.2.mantissa : Int), r.2.exponent⟩
  | _ => ⟨r.2.mantissa, r.2.exponent⟩

/-- The one spelling of a value: `-` before a negative mantissa, and no sign otherwise. -/
def toReading (d : Decimal) : Option Bool × Magnitude :=
  match d.mantissa with
  | .ofNat n => (none, ⟨n, d.exponent⟩)
  | .negSucc n => (some true, ⟨n + 1, d.exponent⟩)

theorem ofReading_toReading (d : Decimal) : ofReading (toReading d) = d := by
  cases d with
  | mk m e =>
    cases m with
    | ofNat n => rfl
    | negSucc n => rfl

/-- The description of `coordinate`: `sign? number`. -/
def syn : Syn Decimal :=
  .map ofReading toReading ofReading_toReading (.seq sign.opt Magnitude.syn)

theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `coordinate`. -/
def grammar : Grammar Decimal := ⟨syn, by decide +kernel, syn_total⟩

/-- An integer, exactly. -/
def ofInt (n : Int) : Decimal := ⟨n, 0⟩

/-- `n / 10 ^ places`, exactly: `ofScaled 125 2` is `1.25`. -/
def ofScaled (n : Int) : Nat → Decimal
  | 0 => ⟨n, 0⟩
  | places + 1 => ⟨n, .negSucc places⟩

/-- A numeral is the integer it writes: `10 : Decimal`. -/
instance (n : Nat) : OfNat Decimal n := ⟨ofInt n⟩

/-- The opposite number, with the same digits: `-10 : Decimal`. -/
instance : Neg Decimal := ⟨fun d => ⟨-d.mantissa, d.exponent⟩⟩

end Decimal

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Decimal.syn_total

/-! ## The zeros at the end of a number

A value is a spelling: `150`, `15e1` and `150.0` are three values that denote one number.
`Whatwg/Svg/Value/Cohort.lean` holds that relation, the canonical value of a number and their
laws. The two definitions here are what a program needs to build a value. -/

namespace Decimal

/-- Move the zeros at the end of a mantissa into the exponent, one for each step. `fuel` bounds
the steps. -/
def stripZeros : Nat → Int → Int → Decimal
  | 0, m, e => ⟨m, e⟩
  | fuel + 1, m, e => if m % 10 = 0 then stripZeros fuel (m / 10) (e + 1) else ⟨m, e⟩

/-- The value of the same number with no zero at the end of its fraction: `10.000` becomes `10`
and `13.250` becomes `13.25`. It takes no exponent from a whole number, so `15000.000` becomes
`15000`, where `tidy` writes `15e3`. The cost is the number of places. A program that counts
in thousandths writes `(ofScaled n 3).trim`. -/
def trim (d : Decimal) : Decimal := stripZeros (-d.exponent).toNat d.mantissa d.exponent

end Decimal

/-! ## A coordinate pair -/

/-- A coordinate pair: the typed value of the production `coordinate_pair`. -/
structure Point where
  x : Decimal
  y : Decimal
  deriving DecidableEq, Repr, Inhabited

namespace Point

/-- The description of `coordinate_pair`: `coordinate comma_wsp? coordinate`, printed with a
comma. -/
def syn : Syn Point :=
  .map (fun p => ⟨p.1, p.2⟩) (fun p => (p.x, p.y)) (fun _ => rfl)
    (.seq Decimal.syn (.right commaSep Decimal.syn))

theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `coordinate_pair`. -/
def grammar : Grammar Point := ⟨syn, by decide +kernel, syn_total⟩

end Point

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Point.syn_total

end Whatwg.Svg.Value
