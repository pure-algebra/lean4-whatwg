import Whatwg.Css.Syntax.Build

/-!
# Whatwg.Css.Syntax.Build.Laws

Owner: what the builders of `Whatwg/Css/Syntax/Build.lean` give (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

A value built with the builders is written by `serialize` and read back by the tokenizer
(`tokenize_serialize` of `Whatwg/Css/Syntax/Laws.lean`) where its tokens are `Writable`. This
module says which builders give such a value for every argument, and what the others ask of
theirs. It says the same of `Quiet`: no comment stands in the text.

How the two tests compose.

- `writable_append`: two writable lists in a row are writable. So a writable value is built
  from writable parts, whatever stands at the place where they meet.
- `quiet_append_whitespace`, `quiet_append_comma`: two quiet lists with a whitespace token, or
  a comma and a whitespace token, between them are quiet. `quiet_function` and `quiet_block`:
  what stands inside a function or a simple block is quiet inside it. Two quiet lists with
  nothing between them need not be quiet: two identifiers in a row are read as one.
- `serialize_of_quiet`: the text of a quiet list is the texts of its tokens, one after another.

The builders, each with what it asks.

| Builder | Writable | Quiet |
| --- | --- | --- |
| `space`, `comma`, `colon` | always | always |
| `ident name` | the name is one the tokenizer can give (`isNameValue`) | always |
| `custom name` | the name holds no U+0000 | always |
| `string text` | the text holds no U+0000 | always |
| `delim c` | `isDelimiter c`, and `c` is no reverse solidus | always |
| `int n`, `thousandths n` | always | always |
| `number q`, `percent q` | `isDecimal q` | always |
| `dimension q unit` | `isDecimal q` and `isUnit unit` | always |
| `px q`, `ms q`, `s q`, `deg q` | `isDecimal q` | always |
| `call name arguments` | a name that is not `url`; writable arguments | the arguments are quiet |
| `parens value`, `brackets value` | the value is writable | the value is quiet |
| `var name fallback` | the name holds no U+0000; the fallback is writable | the fallback is quiet |
| `calc e` | each leaf of `e` is writable | each leaf of `e` is quiet |
| `Value.spaced`, `Value.commas` | each component value is writable | each is quiet |
| `Value.list` | each value is writable | each is quiet |
| `Prelude.class name` | the name is a name | always |
| `Prelude.attr name value` | the name is a name; the value holds no U+0000 | always |
| `Prelude.feature name value` | the name is a name; the value is writable | the value is quiet |

What is proved and what is computed. Each cell above is a theorem of this module. A cell under
"Quiet" that says "always" for a builder of one token is `Component.quiet_token`: a comment
stands between two tokens, and one token has none. Where a cell asks something, a caller gives
it by a test that computes (`by decide`, or a guard). `isDecimal` is proved of a whole number
and of a count of thousandths (`isDecimal_intCast`, `isDecimal_mkRat_thousand`), which is what
the picture kit gives. For any other rational number it is a test that computes: that every
denominator with no prime factor but two and five passes is true and not proved here.

Not in the table, and so judged by the two tests alone: `Component.hash`, `Prelude.type`,
`Prelude.id`, `Prelude.pseudo`, `Prelude.root`, the three selectors of a keyframe, and
`Value.ofText`, whose value is whatever the text reads as.

What this module does not claim. `Writable` is the premise of the tokenizer's round trip, and
this module says when a built value has it. That the parser reads the tokens back as the tree
is the law of slice K4, and it asks more of a value: no white space at its ends, no semicolon
at its top.

The laws of lists of tokens and of rows, of a number, of a function and a block by their code
points, and of an expression of `calc()` depend on `propext` and `Quot.sound` at most. A law of
a builder that takes a `String` (an identifier, a string, a unit, `call`, `var`, a prelude)
also depends on `Classical.choice`, as the builder does, through `String.toList` of core; so do
`isDecimal_mkRat_thousand` and what rests on it, through `mkRat`. No theorem here reaches any
other axiom.
-/

namespace Whatwg.Css.Syntax

/-! ## Writable lists in a row -/

/-- A token that may end a list may stand before any token. -/
theorem Token.mayPrecede_of_mayEnd {a : Token} (h : a.mayEnd = true) (b : Token) :
    a.mayPrecede b = true := by
  cases a with
  | delim c =>
    have hc : (c != '\\') = true := h
    show (c != '\\' || b == .whitespace) = true
    rw [hc]
    rfl
  | badString => exact Bool.noConfusion h
  | function value =>
    have hv : (!isUrlName value) = true := h
    show (!isUrlName value || _) = true
    rw [hv]
    rfl
  | _ => rfl

/-- What is writable after a token is still writable with a writable list after it. -/
theorem writableAfter_append {a : Token} {xs ys : List Token} (hx : writableAfter a xs = true)
    (hy : Writable ys = true) : writableAfter a (xs ++ ys) = true := by
  induction xs generalizing a with
  | nil =>
    have h := Bool.and_eq_true_iff.mp hx
    cases ys with
    | nil => exact hx
    | cons b rest =>
      show (a.writable && a.mayPrecede b && writableAfter b rest) = true
      rw [h.1, Token.mayPrecede_of_mayEnd h.2 b]
      exact hy
  | cons b rest ih =>
    have h := Bool.and_eq_true_iff.mp hx
    show (a.writable && a.mayPrecede b && writableAfter b (rest ++ ys)) = true
    rw [h.1, ih h.2]
    rfl

/-- **Two writable lists in a row are writable.** -/
theorem writable_append {xs ys : List Token} (hx : Writable xs = true) (hy : Writable ys = true) :
    Writable (xs ++ ys) = true := by
  cases xs with
  | nil => exact hy
  | cons a rest => exact writableAfter_append hx hy

/-- A token before a writable list: the token is writable and may end a list. -/
theorem writable_cons {a : Token} {xs : List Token} (ha : a.writable = true)
    (he : a.mayEnd = true) (hx : Writable xs = true) : Writable (a :: xs) = true :=
  writable_append (xs := [a]) (Bool.and_eq_true_iff.mpr ⟨ha, he⟩) hx

/-! ## Quiet lists in a row -/

/-- The table marks no pair whose second token shows up in no column. -/
theorem tableMarks_of_column_none {a b : Token} (h : b.column? = none) :
    tableMarks a b = false := by
  unfold tableMarks
  rw [h]
  cases a.row? <;> rfl

/-- No comment goes before a token that shows up in no column of the table and ends neither of
the two pairs beside it. -/
theorem needsComment_right {b : Token} (hc : b.column? = none) (h₁ : b ≠ .delim '!')
    (h₂ : b ≠ .delim '>') (a : Token) : needsComment a b = false := by
  unfold needsComment extraPairs
  rw [tableMarks_of_column_none hc, beq_false_of_ne h₁, beq_false_of_ne h₂, Bool.and_false,
    Bool.and_false]
  rfl

/-- No comment goes after a whitespace token. -/
theorem needsComment_whitespace_left (b : Token) : needsComment .whitespace b = false := rfl

/-- No comment goes before a whitespace token. -/
theorem needsComment_whitespace_right (a : Token) : needsComment a .whitespace = false :=
  needsComment_right (b := .whitespace) rfl nofun nofun a

/-- No comment goes after a comma. -/
theorem needsComment_comma_left (b : Token) : needsComment .comma b = false := rfl

/-- No comment goes before a comma. -/
theorem needsComment_comma_right (a : Token) : needsComment a .comma = false :=
  needsComment_right (b := .comma) rfl nofun nofun a

/-- A quiet list after a token that needs no comment after it. -/
theorem quiet_cons {a : Token} (ha : ∀ b, needsComment a b = false) (xs : List Token) :
    Quiet (a :: xs) = Quiet xs := by
  cases xs with
  | nil => rfl
  | cons b rest =>
    show (!needsComment a b && Quiet (b :: rest)) = Quiet (b :: rest)
    rw [ha b]
    rfl

/-- **Two lists with a token between them that needs no comment on either side** are quiet
exactly when both are. -/
theorem quiet_append_sep {s : Token} (hl : ∀ a, needsComment a s = false)
    (hr : ∀ b, needsComment s b = false) (xs ys : List Token) :
    Quiet (xs ++ s :: ys) = (Quiet xs && Quiet ys) := by
  induction xs with
  | nil =>
    rw [List.nil_append, quiet_cons hr]
    rfl
  | cons a rest ih =>
    cases rest with
    | nil =>
      show (!needsComment a s && Quiet (s :: ys)) = (true && Quiet ys)
      rw [hl a, quiet_cons hr]
      rfl
    | cons b rest' =>
      show (!needsComment a b && Quiet ((b :: rest') ++ s :: ys)) =
        ((!needsComment a b && Quiet (b :: rest')) && Quiet ys)
      rw [ih, Bool.and_assoc]

/-- **Two lists with a whitespace token between them** are quiet exactly when both are. -/
theorem quiet_append_whitespace (xs ys : List Token) :
    Quiet (xs ++ .whitespace :: ys) = (Quiet xs && Quiet ys) :=
  quiet_append_sep needsComment_whitespace_right needsComment_whitespace_left xs ys

/-- **Two lists with a comma and a whitespace token between them** are quiet exactly when both
are. -/
theorem quiet_append_comma (xs ys : List Token) :
    Quiet (xs ++ .comma :: .whitespace :: ys) = (Quiet xs && Quiet ys) := by
  rw [quiet_append_sep needsComment_comma_right needsComment_comma_left,
    quiet_cons needsComment_whitespace_left]

/-- A list between a function token and a right parenthesis is quiet exactly when it is. -/
theorem quiet_function (name : List Char) (xs : List Token) :
    Quiet (.function name :: (xs ++ [.closeParen])) = Quiet xs := by
  rw [quiet_cons (fun _ => rfl),
    quiet_append_sep (fun a => needsComment_right (b := .closeParen) rfl nofun nofun a)
      (fun _ => rfl)]
  exact Bool.and_true _

/-- A list between the two brackets of a simple block is quiet exactly when it is. -/
theorem quiet_block (bracket : Bracket) (xs : List Token) :
    Quiet (bracket.opening :: (xs ++ [bracket.closing])) = Quiet xs := by
  cases bracket with
  | square =>
    show Quiet (.openSquare :: (xs ++ [.closeSquare])) = Quiet xs
    rw [quiet_cons (fun _ => rfl),
      quiet_append_sep (fun a => needsComment_right (b := .closeSquare) rfl nofun nofun a)
        (fun _ => rfl)]
    exact Bool.and_true _
  | paren =>
    show Quiet (.openParen :: (xs ++ [.closeParen])) = Quiet xs
    rw [quiet_cons (fun _ => rfl),
      quiet_append_sep (fun a => needsComment_right (b := .closeParen) rfl nofun nofun a)
        (fun _ => rfl)]
    exact Bool.and_true _
  | curly =>
    show Quiet (.openCurly :: (xs ++ [.closeCurly])) = Quiet xs
    rw [quiet_cons (fun _ => rfl),
      quiet_append_sep (fun a => needsComment_right (b := .closeCurly) rfl nofun nofun a)
        (fun _ => rfl)]
    exact Bool.and_true _

/-- **The text of a quiet list is the texts of its tokens, one after another**: no comment is
written. -/
theorem serialize_of_quiet : ∀ {tokens : List Token}, Quiet tokens = true →
    serialize tokens = tokens.flatMap Token.text
  | [], _ => rfl
  | [a], _ => by
    show a.text ++ [] = a.text ++ []
    rfl
  | a :: b :: rest, h => by
    have hq : (!needsComment a b && Quiet (b :: rest)) = true := h
    have h' := Bool.and_eq_true_iff.mp hq
    have hn : needsComment a b = false := by
      cases hc : needsComment a b with
      | false => rfl
      | true =>
        rw [hc] at h'
        exact Bool.noConfusion h'.1
    have ih := serialize_of_quiet h'.2
    show a.text ++ (separator a b ++ (b.text ++ serializeAfter b rest)) =
      a.text ++ (b :: rest).flatMap Token.text
    have hs : separator a b = [] := by
      unfold separator
      rw [hn]
      rfl
    rw [hs, List.nil_append]
    exact congrArg (a.text ++ ·) ih

/-! ## The tokens of a row -/

/-- The tokens of a row are those of its first component value and those of the rest. -/
theorem Component.tokensAll_cons (c : Component) (rest : List Component) :
    Component.tokensAll (c :: rest) = c.tokens ++ Component.tokensAll rest := by
  rw [Component.tokensAll]

/-- The tokens of two rows in a row. -/
theorem Component.tokensAll_append (v w : List Component) :
    Component.tokensAll (v ++ w) = Component.tokensAll v ++ Component.tokensAll w := by
  induction v with
  | nil =>
    rw [List.nil_append, Component.tokensAll, List.nil_append]
  | cons c rest ih =>
    rw [List.cons_append, Component.tokensAll_cons, Component.tokensAll_cons, ih,
      List.append_assoc]

/-- The tokens of a row of one component value. -/
theorem Component.tokensAll_singleton (c : Component) : Component.tokensAll [c] = c.tokens := by
  rw [Component.tokensAll_cons, Component.tokensAll, List.append_nil]

namespace Value

/-- A row of one component value is writable exactly when the component value is. -/
theorem writable_singleton (c : Component) : writable [c] = c.writable := by
  rw [writable, Component.tokensAll_singleton]
  rfl

/-- A row of one component value is quiet exactly when the component value is. -/
theorem quiet_singleton (c : Component) : quiet [c] = c.quiet := by
  rw [quiet, Component.tokensAll_singleton]
  rfl

/-- **Two writable values in a row are writable.** -/
theorem writable_append {v w : Value} (hv : v.writable = true) (hw : w.writable = true) :
    writable (v ++ w) = true := by
  rw [writable, Component.tokensAll_append]
  exact Syntax.writable_append hv hw

/-- A writable component value before a writable value. -/
theorem writable_cons {c : Component} {v : Value} (hc : c.writable = true)
    (hv : v.writable = true) : writable (c :: v) = true := by
  rw [writable, Component.tokensAll_cons]
  exact Syntax.writable_append hc hv

/-- A whitespace token before a value: quiet exactly when the value is. -/
theorem quiet_space_cons (v : Value) : quiet (Component.space :: v) = v.quiet :=
  quiet_cons needsComment_whitespace_left _

/-- A component value, a whitespace token and a value are quiet exactly when the component value
and the value are. -/
theorem quiet_cons_space (c : Component) (v : Value) :
    quiet (c :: .space :: v) = (c.quiet && v.quiet) := by
  rw [quiet, Component.tokensAll_cons, Component.tokensAll_cons]
  exact quiet_append_whitespace _ _

/-- A component value, a comma, a whitespace token and a value are quiet exactly when the
component value and the value are. -/
theorem quiet_cons_comma (c : Component) (v : Value) :
    quiet (c :: .comma :: .space :: v) = (c.quiet && v.quiet) := by
  rw [quiet, Component.tokensAll_cons, Component.tokensAll_cons, Component.tokensAll_cons]
  exact quiet_append_comma _ _

/-- **A row with spaces is writable** where each of its component values is. -/
theorem writable_spaced : ∀ {cs : List Component}, (∀ c ∈ cs, c.writable = true) →
    (spaced cs).writable = true
  | [], _ => rfl
  | [c], h => (writable_singleton c).trans (h c List.mem_cons_self)
  | c :: d :: rest, h =>
    writable_cons (h c List.mem_cons_self)
      (writable_cons (c := .space) rfl
        (writable_spaced (cs := d :: rest) fun x hx => h x (List.mem_cons_of_mem c hx)))

/-- **A row with spaces is quiet exactly when each of its component values is.** -/
theorem quiet_spaced : ∀ cs : List Component, (spaced cs).quiet = cs.all Component.quiet
  | [] => rfl
  | [c] => by
    rw [spaced, quiet_singleton, List.all_cons, List.all_nil, Bool.and_true]
  | c :: d :: rest => by
    rw [spaced, quiet_cons_space, quiet_spaced (d :: rest)]
    rfl

/-- **A row with commas is writable** where each of its component values is. -/
theorem writable_commas : ∀ {cs : List Component}, (∀ c ∈ cs, c.writable = true) →
    (commas cs).writable = true
  | [], _ => rfl
  | [c], h => (writable_singleton c).trans (h c List.mem_cons_self)
  | c :: d :: rest, h =>
    writable_cons (h c List.mem_cons_self)
      (writable_cons (c := .comma) rfl
        (writable_cons (c := .space) rfl
          (writable_commas (cs := d :: rest) fun x hx => h x (List.mem_cons_of_mem c hx))))

/-- **A row with commas is quiet exactly when each of its component values is.** -/
theorem quiet_commas : ∀ cs : List Component, (commas cs).quiet = cs.all Component.quiet
  | [] => rfl
  | [c] => by
    rw [commas, quiet_singleton, List.all_cons, List.all_nil, Bool.and_true]
  | c :: d :: rest => by
    rw [commas, quiet_cons_comma, quiet_commas (d :: rest)]
    rfl

/-- **A list of values is writable** where each value is. -/
theorem writable_list : ∀ {vs : List Value}, (∀ v ∈ vs, v.writable = true) →
    (list vs).writable = true
  | [], _ => rfl
  | [v], h => h v List.mem_cons_self
  | v :: w :: rest, h =>
    writable_append (h v List.mem_cons_self)
      (writable_cons (c := .comma) rfl
        (writable_cons (c := .space) rfl
          (writable_list (vs := w :: rest) fun x hx => h x (List.mem_cons_of_mem v hx))))

/-- **A list of values is quiet exactly when each value is.** -/
theorem quiet_list : ∀ vs : List Value, (list vs).quiet = vs.all quiet
  | [] => rfl
  | [v] => by
    rw [list, List.all_cons, List.all_nil, Bool.and_true]
  | v :: w :: rest => by
    have h : quiet (v ++ Component.comma :: Component.space :: list (w :: rest)) =
        (v.quiet && (list (w :: rest)).quiet) := by
      rw [quiet, Component.tokensAll_append, Component.tokensAll_cons, Component.tokensAll_cons]
      exact quiet_append_comma _ _
    rw [list, h, quiet_list (w :: rest)]
    rfl

end Value

/-! ## Numbers -/

/-- **The number that a builder makes is writable exactly when it has a decimal text.** Its
sign character agrees with its value, and its type is "integer" exactly where it is whole, both
by the way it is made. -/
theorem Numeric.writable_of (q : Rat) :
    (Numeric.of q).writable (NumberFlag.of q) = isDecimal q := by
  have whole : q.den = 1 → isDecimal q = true := fun hd => by
    unfold isDecimal
    rw [hd, Nat.mod_one]
    rfl
  by_cases hs : q.num < 0
  · have hn : Numeric.of q = { value := q, sign := some .minus } := by
      unfold Numeric.of
      rw [if_pos hs]
    have hle : decide (q.num ≤ 0) = true := decide_eq_true (Int.le_of_lt hs)
    by_cases hd : q.den = 1
    · have hf : NumberFlag.of q = .integer := if_pos hd
      rw [hn, hf, whole hd]
      show (decide (q.num ≤ 0) && (q.den == 1)) = true
      rw [hle, hd]
      rfl
    · have hf : NumberFlag.of q = .number := if_neg hd
      rw [hn, hf]
      show (decide (q.num ≤ 0) && (10 ^ max 1 (fractionDigits q.den) % q.den == 0)) = isDecimal q
      rw [hle]
      rfl
  · have hn : Numeric.of q = { value := q, sign := none } := by
      unfold Numeric.of
      rw [if_neg hs]
    have hle : decide (0 ≤ q.num) = true := decide_eq_true (Int.not_lt.mp hs)
    by_cases hd : q.den = 1
    · have hf : NumberFlag.of q = .integer := if_pos hd
      rw [hn, hf, whole hd]
      show (decide (0 ≤ q.num) && (q.den == 1)) = true
      rw [hle, hd]
      rfl
    · have hf : NumberFlag.of q = .number := if_neg hd
      rw [hn, hf]
      show (decide (0 ≤ q.num) && (10 ^ max 1 (fractionDigits q.den) % q.den == 0)) = isDecimal q
      rw [hle]
      rfl

/-- A whole number has a decimal text. -/
theorem isDecimal_intCast (n : Int) : isDecimal (n : Rat) = true := by
  unfold isDecimal
  rw [Rat.den_intCast, Nat.mod_one]
  rfl

/-- Every divisor of a thousand divides the power of ten that the writer finds for it. -/
theorem decimal_of_dvd_thousand :
    ∀ d : Nat, d ≤ 1000 → 1000 % d = 0 → 10 ^ max 1 (fractionDigits d) % d = 0 := by
  decide +kernel

/-- **A count of thousandths has a decimal text.** So a builder that is given one writes a
number that the tokenizer reads back, whatever the count. -/
theorem isDecimal_mkRat_thousand (n : Int) : isDecimal (mkRat n 1000) = true := by
  have hd : (mkRat n 1000).den ∣ 1000 := by
    rw [Rat.den_mkRat, if_neg (by decide)]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have h := decimal_of_dvd_thousand _ (Nat.le_of_dvd (by decide) hd) (Nat.mod_eq_zero_of_dvd hd)
  unfold isDecimal
  rw [h]
  rfl

/-! ## One component value -/

namespace Component

/-- A whitespace token is writable and quiet. -/
theorem writable_space : space.writable = true := rfl

/-- A comma is writable. -/
theorem writable_comma : comma.writable = true := rfl

/-- A colon is writable. -/
theorem writable_colon : colon.writable = true := rfl

/-- **A component value of one token is quiet**: a comment stands between two tokens. -/
theorem quiet_token (t : Token) : (Component.token t).quiet = true := rfl

/-- An identifier is writable exactly when its name is one the tokenizer can give: at least one
code point, and no U+0000. -/
theorem writable_ident (name : String) : (ident name).writable = isNameValue name.toList :=
  Bool.and_true _

/-- A string is writable exactly when it holds no U+0000. -/
theorem writable_string (text : String) :
    (string text).writable = text.toList.all fun c => c.toNat != 0 :=
  Bool.and_true _

/-- A delimiter is writable exactly when the tokenizer gives its code point as a delimiter and
it is no reverse solidus, which a whitespace token has to follow. -/
theorem writable_delim (c : Char) : (delim c).writable = (isDelimiter c && c != '\\') := rfl

/-- **A number is writable exactly when it has a decimal text.** -/
theorem writable_number (q : Rat) : (number q).writable = isDecimal q :=
  (Bool.and_true _).trans (Numeric.writable_of q)

/-- **A whole number is writable.** -/
theorem writable_int (n : Int) : (int n).writable = true :=
  (writable_number n).trans (isDecimal_intCast n)

/-- **A count of thousandths is writable.** -/
theorem writable_thousandths (n : Int) : (thousandths n).writable = true :=
  (writable_number _).trans (isDecimal_mkRat_thousand n)

/-- **A dimension is writable exactly when its number has a decimal text and its unit is a plain
identifier that is not read as an exponent.** -/
theorem writable_dimension (q : Rat) (unit : String) :
    (dimension q unit).writable = (isDecimal q && isUnit unit) := by
  show ((Numeric.of q).writable (NumberFlag.of q) && isPlainIdentifier unit.toList &&
    !readsAsExponent unit.toList && true) = (isDecimal q && isUnit unit)
  rw [Numeric.writable_of, Bool.and_true, Bool.and_assoc]
  rfl

/-- A length in pixels is writable exactly when its number has a decimal text. -/
theorem writable_px (q : Rat) : (px q).writable = isDecimal q := by
  have hu : isUnit "px" = true := by decide +kernel
  rw [px, writable_dimension, hu, Bool.and_true]

/-- A time in milliseconds is writable exactly when its number has a decimal text. -/
theorem writable_ms (q : Rat) : (ms q).writable = isDecimal q := by
  have hu : isUnit "ms" = true := by decide +kernel
  rw [ms, writable_dimension, hu, Bool.and_true]

/-- A time in seconds is writable exactly when its number has a decimal text. -/
theorem writable_s (q : Rat) : (s q).writable = isDecimal q := by
  have hu : isUnit "s" = true := by decide +kernel
  rw [s, writable_dimension, hu, Bool.and_true]

/-- An angle in degrees is writable exactly when its number has a decimal text. -/
theorem writable_deg (q : Rat) : (deg q).writable = isDecimal q := by
  have hu : isUnit "deg" = true := by decide +kernel
  rw [deg, writable_dimension, hu, Bool.and_true]

/-- A per cent is writable exactly when its number has a decimal text. -/
theorem writable_percent (q : Rat) : (percent q).writable = isDecimal q :=
  (Bool.and_true _).trans (Numeric.writable_of q)

/-- **A function is writable** where its name is one the tokenizer can give and is not `url`,
and its arguments are writable. A function named `url` is writable only before a string, and
this law does not cover it. -/
theorem writable_function {name : List Char} {arguments : Value}
    (hn : isNameValue name = true) (hu : isUrlName name = false)
    (ha : arguments.writable = true) : (Component.function name arguments).writable = true := by
  have he : (Token.function name).mayEnd = true := by
    show (!isUrlName name) = true
    rw [hu]
    rfl
  exact Syntax.writable_cons (a := .function name) hn he
    (Syntax.writable_append ha (xs := Component.tokensAll arguments) (ys := [.closeParen]) rfl)

/-- **A function is quiet exactly when its arguments are.** -/
theorem quiet_function (name : List Char) (arguments : Value) :
    (Component.function name arguments).quiet = arguments.quiet :=
  Syntax.quiet_function name _

/-- `Component.call` is the function of the name's code points. -/
theorem writable_call {name : String} {arguments : Value} (hn : isNameValue name.toList = true)
    (hu : isUrlName name.toList = false) (ha : arguments.writable = true) :
    (call name arguments).writable = true :=
  writable_function hn hu ha

/-- A function is quiet exactly when its arguments are. -/
theorem quiet_call (name : String) (arguments : Value) :
    (call name arguments).quiet = arguments.quiet :=
  Syntax.quiet_function _ _

/-- **A simple block is writable** where its value is. -/
theorem writable_block (bracket : Bracket) {value : Value} (hv : value.writable = true) :
    (Component.block bracket value).writable = true := by
  have ho : bracket.opening.writable = true ∧ bracket.opening.mayEnd = true := by
    cases bracket <;> exact ⟨rfl, rfl⟩
  have hc : Writable [bracket.closing] = true := by
    cases bracket <;> rfl
  exact Syntax.writable_cons ho.1 ho.2 (Syntax.writable_append hv hc)

/-- **A simple block is quiet exactly when its value is.** -/
theorem quiet_block (bracket : Bracket) (value : Value) :
    (Component.block bracket value).quiet = value.quiet :=
  Syntax.quiet_block bracket _

/-- The name of a custom property is a name exactly when the name it was given has no
U+0000. -/
theorem isNameValue_dashed (name : List Char) :
    isNameValue (dashed name) = name.all fun c => c.toNat != 0 := by
  unfold dashed
  split <;> rfl

/-- The name of a custom property is writable exactly when it holds no U+0000. -/
theorem writable_custom (name : String) :
    (custom name).writable = name.toList.all fun c => c.toNat != 0 :=
  (Bool.and_true _).trans (isNameValue_dashed name.toList)

/-- **A reference to a custom property is writable** where its name holds no U+0000 and its
fallback is writable. -/
theorem writable_var {name : String} {fallback : Value}
    (hn : (name.toList.all fun c => c.toNat != 0) = true) (hf : fallback.writable = true) :
    (var name fallback).writable = true := by
  refine writable_function (by decide) (by decide) ?_
  refine Value.writable_cons ((writable_custom name).trans hn) ?_
  split
  · rfl
  · exact Value.writable_cons writable_comma (Value.writable_cons writable_space hf)

/-- **A reference to a custom property is quiet exactly when its fallback is.** -/
theorem quiet_var (name : String) (fallback : Value) :
    (var name fallback).quiet = fallback.quiet := by
  rw [var, quiet_function]
  by_cases he : fallback.isEmpty = true
  · rw [if_pos he, Value.quiet_singleton, List.isEmpty_iff.mp he]
    rfl
  · rw [if_neg he, Value.quiet_cons_comma]
    rfl

end Component

/-! ## An expression of `calc()` -/

namespace Calc

/-- A value in parentheses, or as it is, is writable where it is. -/
theorem writable_group (wrap : Bool) {v : Value} (hv : v.writable = true) :
    (group wrap v).writable = true := by
  cases wrap with
  | false => exact hv
  | true => exact (Value.writable_singleton _).trans (Component.writable_block .paren hv)

/-- A value in parentheses, or as it is, is quiet exactly when it is. -/
theorem quiet_group (wrap : Bool) (v : Value) : (group wrap v).quiet = v.quiet := by
  cases wrap with
  | false => rfl
  | true => exact (Value.quiet_singleton _).trans (Component.quiet_block .paren v)

/-- Two writable values with one of the four operators between them are writable. -/
theorem writable_around {op : Char} (ho : (isDelimiter op && op != '\\') = true) {a b : Value}
    (ha : a.writable = true) (hb : b.writable = true) : (around op a b).writable = true :=
  Value.writable_append ha
    (Value.writable_cons Component.writable_space
      (Value.writable_cons ((Component.writable_delim op).trans ho)
        (Value.writable_cons Component.writable_space hb)))

/-- Two values with an operator between them are quiet exactly when both are: the operator has
a whitespace token on each side. -/
theorem quiet_around (op : Char) (a b : Value) :
    (around op a b).quiet = (a.quiet && b.quiet) := by
  show Quiet (Component.tokensAll (a ++ Component.space :: Component.delim op ::
    Component.space :: b)) = (a.quiet && b.quiet)
  rw [Component.tokensAll_append, Component.tokensAll_cons, Component.tokensAll_cons,
    Component.tokensAll_cons]
  show Quiet (Component.tokensAll a ++ Token.whitespace :: ([Token.delim op] ++
    Token.whitespace :: Component.tokensAll b)) = (a.quiet && b.quiet)
  rw [quiet_append_whitespace, quiet_append_whitespace]
  rfl

/-- **The components of an expression are writable** where each of its leaves is. -/
theorem value_writable : ∀ {e : Calc}, e.writable = true → e.value.writable = true
  | .leaf c, h => (Value.writable_singleton c).trans h
  | .add a b, h =>
    writable_around (by decide) (value_writable (Bool.and_eq_true_iff.mp h).1)
      (value_writable (Bool.and_eq_true_iff.mp h).2)
  | .sub a b, h =>
    writable_around (by decide) (value_writable (Bool.and_eq_true_iff.mp h).1)
      (writable_group _ (value_writable (Bool.and_eq_true_iff.mp h).2))
  | .mul a b, h =>
    writable_around (by decide) (writable_group _ (value_writable (Bool.and_eq_true_iff.mp h).1))
      (writable_group _ (value_writable (Bool.and_eq_true_iff.mp h).2))
  | .div a b, h =>
    writable_around (by decide) (writable_group _ (value_writable (Bool.and_eq_true_iff.mp h).1))
      (writable_group _ (value_writable (Bool.and_eq_true_iff.mp h).2))

/-- **The components of an expression are quiet exactly when each of its leaves is.** -/
theorem value_quiet : ∀ e : Calc, e.value.quiet = e.quiet
  | .leaf c => Value.quiet_singleton c
  | .add a b => by
    rw [value, quiet_around, value_quiet a, value_quiet b, quiet]
  | .sub a b => by
    rw [value, quiet_around, quiet_group, value_quiet a, value_quiet b, quiet]
  | .mul a b => by
    rw [value, quiet_around, quiet_group, quiet_group, value_quiet a, value_quiet b, quiet]
  | .div a b => by
    rw [value, quiet_around, quiet_group, quiet_group, value_quiet a, value_quiet b, quiet]

end Calc

namespace Component

/-- **`calc()` of an expression is writable** where each leaf of the expression is. -/
theorem writable_calc {e : Calc} (h : e.writable = true) :
    (Component.calc e).writable = true :=
  writable_function (by decide) (by decide) (Calc.value_writable h)

/-- **`calc()` of an expression is quiet exactly when each leaf of the expression is.** -/
theorem quiet_calc (e : Calc) : (Component.calc e).quiet = e.quiet :=
  (quiet_function _ _).trans (Calc.value_quiet e)

end Component

/-! ## Preludes -/

namespace Prelude

/-- A class selector is quiet: a full stop and an identifier need no comment. -/
theorem quiet_class (name : String) : Value.quiet (Prelude.class name) = true := rfl

/-- A class selector is writable where its name is one the tokenizer can give. -/
theorem writable_class {name : String} (hn : isNameValue name.toList = true) :
    Value.writable (Prelude.class name) = true :=
  Value.writable_cons (c := .delim '.') rfl
    ((Value.writable_singleton _).trans ((Component.writable_ident name).trans hn))

/-- **An attribute selector with a value is quiet.** -/
theorem quiet_attr (name value : String) : Value.quiet (attr name value) = true := by
  rw [attr, Value.quiet_singleton]
  show Component.quiet (.block .square [.ident name, .delim '=', .string value]) = true
  rw [Component.quiet_block]
  show (!needsComment (.ident name.toList) (.delim '=') &&
    Quiet [Token.delim '=', Token.string value.toList]) = true
  rw [needsComment_right (b := .delim '=') rfl (by decide) (by decide)]
  rfl

/-- **An attribute selector with a value is writable** where its name is one the tokenizer can
give and its value holds no U+0000. The value is a string, so any other text is written. -/
theorem writable_attr {name value : String} (hn : isNameValue name.toList = true)
    (hv : (value.toList.all fun c => c.toNat != 0) = true) :
    Value.writable (attr name value) = true := by
  rw [attr, Value.writable_singleton]
  exact Component.writable_block .square
    (Value.writable_cons ((Component.writable_ident name).trans hn)
      (Value.writable_cons (c := .delim '=') rfl
        ((Value.writable_singleton _).trans ((Component.writable_string value).trans hv))))

/-- **A media feature is quiet exactly when its value is.** -/
theorem quiet_feature (name : String) (value : Value) :
    Value.quiet (feature name value) = value.quiet := by
  have hc : Quiet [Token.ident name.toList, Token.colon] = true := by
    show (!needsComment (.ident name.toList) .colon && true) = true
    rw [needsComment_right (b := .colon) rfl nofun nofun]
    rfl
  rw [feature, Value.quiet_singleton]
  show Component.quiet (.block .paren (.ident name :: .colon :: .space :: value)) = value.quiet
  rw [Component.quiet_block]
  show Quiet (Component.tokensAll (.ident name :: .colon :: .space :: value)) = value.quiet
  rw [Component.tokensAll_cons, Component.tokensAll_cons, Component.tokensAll_cons]
  show Quiet ([Token.ident name.toList, Token.colon] ++
    Token.whitespace :: Component.tokensAll value) = value.quiet
  rw [quiet_append_whitespace, hc]
  rfl

/-- **A media feature is writable** where its name is one the tokenizer can give and its value
is writable. -/
theorem writable_feature {name : String} {value : Value} (hn : isNameValue name.toList = true)
    (hv : value.writable = true) : Value.writable (feature name value) = true := by
  rw [feature, Value.writable_singleton]
  exact Component.writable_block .paren
    (Value.writable_cons ((Component.writable_ident name).trans hn)
      (Value.writable_cons Component.writable_colon
        (Value.writable_cons Component.writable_space hv)))

end Prelude

end Whatwg.Css.Syntax
