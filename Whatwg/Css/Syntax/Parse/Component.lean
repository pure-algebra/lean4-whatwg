import Whatwg.Css.Syntax.Readable

/-!
# Whatwg.Css.Syntax.Parse.Component

Owner: the round trip of parsing at component values (slice K4 of `docs/CSS-PACKAGE-PLAN.md`;
proof graph `CSS-PG-SYNTAX`).

- `Component.read`: **consuming the tokens of a readable component value gives the value**, and
  the tokens after it.
- `Component.readAll`: the loop over the tokens of a readable row gives the row, and goes on
  with what follows the row.
- `consumeUntil_tokensAll`, `consumeListOfComponentValues_tokensAll`: before a list that stops
  the row, the row and that list.
- `parseComponentValues_tokensAll`: **parsing the tokens of a list of readable component values
  gives the list.**
- `parseComponentValue_tokens`: the same for one component value that is not white space.

The first lemmas say how each function steps, with no word of how Lean was shown that it ends.
-/

namespace Whatwg.Css.Syntax

/-! ## How the functions step -/

theorem consumeComponentValue_cons (token : Token) (rest : List Token) :
    consumeComponentValue (token :: rest) = some (consumeComponentValueSized token rest).val :=
  rfl

/-- A preserved token is its own component value. -/
theorem consumeComponentValueSized_preserved {t : Token} (h : t.preserved = true)
    (rest : List Token) : (consumeComponentValueSized t rest).val = (.token t, rest) :=
  congrArg Subtype.val (consumeComponentValueSized.eq_5 t rest
    (fun e => by subst e; cases h) (fun e => by subst e; cases h) (fun e => by subst e; cases h)
    (fun name e => by subst e; cases h))

/-- A token that opens a block: the block's value is gathered up to the token that closes it,
and that token is discarded. -/
theorem consumeComponentValueSized_opening (bracket : Bracket) (rest : List Token) :
    (consumeComponentValueSized bracket.opening rest).val =
      (.block bracket (consumeUntil (· == bracket.closing) rest).1,
        (consumeUntil (· == bracket.closing) rest).2.drop 1) := by
  cases bracket
  · show (consumeComponentValueSized .openSquare rest).val = _
    rw [consumeComponentValueSized, consumeSimpleBlockSized]
    rfl
  · show (consumeComponentValueSized .openParen rest).val = _
    rw [consumeComponentValueSized, consumeSimpleBlockSized]
    rfl
  · show (consumeComponentValueSized .openCurly rest).val = _
    rw [consumeComponentValueSized, consumeSimpleBlockSized]
    rfl

/-- A function token: the function's value is gathered up to a right parenthesis, and that token
is discarded. -/
theorem consumeComponentValueSized_function (name : List Char) (rest : List Token) :
    (consumeComponentValueSized (.function name) rest).val =
      (.function name (consumeUntil (· == .closeParen) rest).1,
        (consumeUntil (· == .closeParen) rest).2.drop 1) := by
  rw [consumeComponentValueSized, consumeFunctionSized]
  rfl

/-- `consume-simple-block` is the step of `consume-component-value` at the token that opens the
block. -/
theorem consumeSimpleBlock_eq (bracket : Bracket) (input : List Token) :
    consumeSimpleBlock bracket input =
      (.block bracket (consumeUntil (· == bracket.closing) input).1,
        (consumeUntil (· == bracket.closing) input).2.drop 1) := by
  unfold consumeSimpleBlock
  rw [consumeSimpleBlockSized]
  rfl

/-- `consume-function` is the step of `consume-component-value` at a function token. -/
theorem consumeFunction_eq (name : List Char) (input : List Token) :
    consumeFunction name input =
      (.function name (consumeUntil (· == .closeParen) input).1,
        (consumeUntil (· == .closeParen) input).2.drop 1) := by
  unfold consumeFunction
  rw [consumeFunctionSized]
  rfl

/-- The loop at a token that does not end it: a component value, and the loop again. -/
theorem consumeUntil_step {ends : Token → Bool} {input rest : List Token} {c : Component}
    (hc : consumeComponentValue input = some (c, rest))
    (he : ∀ t, input.head? = some t → ends t = false) :
    consumeUntil ends input = (c :: (consumeUntil ends rest).1, (consumeUntil ends rest).2) := by
  cases input with
  | nil => cases hc
  | cons token tail =>
    have hv : (consumeComponentValueSized token tail).val = (c, rest) := Option.some.inj hc
    have hne : ¬ends token = true := by
      rw [he token rfl]
      exact Bool.false_ne_true
    unfold consumeUntil
    rw [consumeUntilSized, if_neg hne]
    show ((consumeComponentValueSized token tail).val.1 ::
        (consumeUntilSized ends (consumeComponentValueSized token tail).val.2).val.1,
      (consumeUntilSized ends (consumeComponentValueSized token tail).val.2).val.2) = _
    rw [hv]

/-- The loop before a list that stops it gathers nothing. -/
theorem consumeUntil_of_stopsAt {ends : Token → Bool} {rest : List Token}
    (h : stopsAt ends rest = true) : consumeUntil ends rest = ([], rest) := by
  cases rest with
  | nil => exact consumeUntil_nil ends
  | cons token tail => exact consumeUntil_of_ends tail h

/-! ## The tokens of a tree -/

theorem Component.tokensAll_nil : Component.tokensAll [] = [] := by
  rw [Component.tokensAll]

theorem Component.tokensAll_cons (c : Component) (rest : List Component) :
    Component.tokensAll (c :: rest) = c.tokens ++ Component.tokensAll rest := by
  rw [Component.tokensAll]

theorem Component.tokensAll_append (a b : List Component) :
    Component.tokensAll (a ++ b) = Component.tokensAll a ++ Component.tokensAll b := by
  induction a with
  | nil => rw [Component.tokensAll_nil, List.nil_append, List.nil_append]
  | cons c rest ih =>
    rw [List.cons_append, Component.tokensAll_cons, Component.tokensAll_cons, ih,
      List.append_assoc]

/-- The tokens of a component value open with its first token. -/
theorem Component.head?_tokens_append (c : Component) (rest : List Token) :
    (c.tokens ++ rest).head? = some c.head := by
  cases c <;> rw [Component.tokens] <;> rfl

/-- A component value that is not white space does not open with a whitespace token. -/
theorem Component.head_ne_whitespace {c : Component} (h : c.isWhitespace = false) :
    c.head ≠ .whitespace := by
  intro heq
  cases c with
  | token t =>
    rw [Component.head] at heq
    subst heq
    cases h
  | function name value => cases heq
  | block bracket value => cases bracket <;> cases heq

/-- "Discard whitespace" before a token that is not white space discards nothing. -/
theorem discardWhitespace_of_head {input : List Token} {token : Token}
    (h : input.head? = some token) (hne : token ≠ .whitespace) :
    discardWhitespace input = input :=
  discardWhitespace.eq_2 input fun rest e => by
    subst e
    exact hne (Option.some.inj h).symm

theorem Component.readableAll_cons {ends : Token → Bool} {c : Component}
    {rest : List Component} (h : Component.readableAll ends (c :: rest) = true) :
    ends c.head = false ∧ c.readable = true ∧ Component.readableAll ends rest = true := by
  rw [Component.readableAll, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem Component.readableAll_append {ends : Token → Bool} {a b : List Component}
    (ha : Component.readableAll ends a = true) (hb : Component.readableAll ends b = true) :
    Component.readableAll ends (a ++ b) = true := by
  induction a with
  | nil => exact hb
  | cons c rest ih =>
    have h := Component.readableAll_cons ha
    rw [List.cons_append, Component.readableAll, ih h.2.2, h.1, h.2.1]
    rfl

/-! ## The round trip at component values -/

mutual

/-- **Consuming the tokens of a readable component value gives the value**, and the tokens after
it. -/
theorem Component.read : ∀ (c : Component), c.readable = true → ∀ (rest : List Token),
    consumeComponentValue (c.tokens ++ rest) = some (c, rest)
  | .token t, h, rest => by
    rw [Component.readable] at h
    rw [Component.tokens, List.singleton_append, consumeComponentValue_cons,
      consumeComponentValueSized_preserved h]
  | .function name value, h, rest => by
    rw [Component.readable] at h
    have ih := Component.readAll (· == .closeParen) value h (.closeParen :: rest)
    rw [consumeUntil_of_ends (ends := (· == Token.closeParen)) rest (beq_self_eq_true _),
      List.append_nil] at ih
    rw [Component.tokens, List.cons_append, List.append_assoc, List.singleton_append,
      consumeComponentValue_cons, consumeComponentValueSized_function, ih]
    rfl
  | .block bracket value, h, rest => by
    rw [Component.readable] at h
    have ih := Component.readAll (· == bracket.closing) value h (bracket.closing :: rest)
    rw [consumeUntil_of_ends (ends := (· == bracket.closing)) rest (beq_self_eq_true _),
      List.append_nil] at ih
    rw [Component.tokens, List.cons_append, List.append_assoc, List.singleton_append,
      consumeComponentValue_cons, consumeComponentValueSized_opening, ih]
    rfl

/-- **The loop over the tokens of a readable row gives the row**, and goes on with what follows
the row. -/
theorem Component.readAll : ∀ (ends : Token → Bool) (value : List Component),
    Component.readableAll ends value = true → ∀ (rest : List Token),
    consumeUntil ends (Component.tokensAll value ++ rest) =
      (value ++ (consumeUntil ends rest).1, (consumeUntil ends rest).2)
  | _, [], _, rest => by
    rw [Component.tokensAll_nil, List.nil_append, List.nil_append]
  | ends, c :: more, h, rest => by
    have hc := Component.readableAll_cons h
    have ih := Component.readAll ends more hc.2.2 rest
    have hread := Component.read c hc.2.1 (Component.tokensAll more ++ rest)
    rw [Component.tokensAll_cons, List.append_assoc,
      consumeUntil_step hread (fun t ht => by
        rw [Component.head?_tokens_append] at ht
        cases ht
        exact hc.1), ih]
    rfl

end

/-- The loop over the tokens of a readable row, before a list that stops it: the row and that
list. -/
theorem consumeUntil_tokensAll {ends : Token → Bool} {value : List Component}
    (h : Component.readableAll ends value = true) {rest : List Token}
    (hrest : stopsAt ends rest = true) :
    consumeUntil ends (Component.tokensAll value ++ rest) = (value, rest) := by
  rw [Component.readAll ends value h rest, consumeUntil_of_stopsAt hrest, List.append_nil]

/-- `consume a list of component values` over the tokens of a readable row, before a list that
stops it: the row and that list. -/
theorem consumeListOfComponentValues_tokensAll {stop : Option Token} {nested : Bool}
    {value : List Component} (h : Component.readableAll (endsList stop nested) value = true)
    {rest : List Token} (hrest : stopsAt (endsList stop nested) rest = true) :
    consumeListOfComponentValues stop nested (Component.tokensAll value ++ rest) = (value, rest) :=
  consumeUntil_tokensAll h hrest

/-- At the top, with no stop token, no token ends a list of component values. -/
theorem endsList_none_false (token : Token) : endsList none false token = false := rfl

/-- **Parsing the tokens of a list of component values gives the list**, where each is readable.
This is `parse a list of component values` after the writer of `Component.tokensAll`: a right
parenthesis, a right square bracket and a right curly bracket may stand at the top of the list,
as preserved tokens. -/
theorem parseComponentValues_tokensAll (value : List Component)
    (h : Component.readableAll (fun _ => false) value = true) :
    parseComponentValues (Component.tokensAll value) = value := by
  have h' := consumeUntil_tokensAll (ends := fun _ => false) h (rest := []) rfl
  rw [List.append_nil] at h'
  show (consumeUntil (endsList none false) (Component.tokensAll value)).1 = value
  have hfun : endsList none false = fun _ => false := funext endsList_none_false
  rw [hfun, h']

/-- **Parsing the tokens of one component value gives the value**, where it is readable and is
not white space, which `parse a component value` discards. -/
theorem parseComponentValue_tokens (c : Component) (h : c.readable = true)
    (hws : c.isWhitespace = false) : parseComponentValue c.tokens = some c := by
  have hd : discardWhitespace (c.tokens ++ []) = c.tokens ++ [] :=
    discardWhitespace_of_head (Component.head?_tokens_append c [])
      (Component.head_ne_whitespace hws)
  have hread := Component.read c h []
  rw [List.append_nil] at hread hd
  unfold parseComponentValue
  rw [hd, hread]
  rfl

end Whatwg.Css.Syntax
