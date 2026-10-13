import Whatwg.Css.Syntax.Write

/-!
# Whatwg.Css.Syntax.Parse

Owner: the parser of CSS (slice K4 of `docs/CSS-PACKAGE-PLAN.md`; rulings CS-6 and CS-9; proof
graph `CSS-PG-SYNTAX`).

The authority is CSS Syntax Module Level 3, sealed at
`vendor/w3c-csswg-drafts-50337328/css-syntax-3/Overview.bs`: the chapter under the heading
`parsing`. Each algorithm under `parser-algorithms` and each entry point under
`parser-entry-points` is one function here, named after it, and its docstring names the
algorithm by its heading identifier.

What this module gives.

- The algorithms: `consumeComponentValue`, `consumeSimpleBlock`, `consumeFunction`,
  `consumeListOfComponentValues`, `consumeRemnantsOfBadDeclaration`, `consumeDeclaration`,
  `consumeAtRule`, `consumeQualifiedRule`, `consumeBlock`, `consumeBlockContents`,
  `consumeStylesheetContents`, `consumeStyleAttribute`.
- The entry points, over tokens: `parseStylesheet`, `parseStylesheetContents`,
  `parseBlockContents`, `parseStyleAttribute`, `parseRule`, `parseDeclaration`,
  `parseComponentValue`, `parseComponentValues`, `parseCommaSeparatedComponentValues`.
- The same over text, through `tokenizeText`: `parseStylesheetText` and the others that end in
  `Text`.

How the standard's words are read here.

- A *token stream* is a list of tokens, and its *next token* is the head of the list. The EOF
  token is the empty list. To *consume* or *discard a token* is to go on with the tail. An
  algorithm returns its result and the tokens after it.
- To *mark* a stream and *restore a mark* is to hand the same list to a second reader:
  `consumeBlockContents` reads a list as a declaration, and where that gives nothing it reads the
  same list as a qualified rule.
- An algorithm that the standard opens with "Assert: the next token is" takes that token's
  content as an argument and reads the tokens after it: `consumeSimpleBlock` takes the bracket,
  `consumeFunction` and `consumeAtRule` take the name, `consumeBlock` reads after the left curly
  bracket.
- The standard's `process` is a loop over the next token. Three algorithms gather component
  values in such a loop until a token ends it: `consume a list of component values`, and the
  preludes of `consume a qualified rule` and `consume an at-rule`. The loops of `consume a simple
  block` and `consume a function` are the same up to their ending token. They are one function
  here, `consumeUntil`, given the tokens that end it.
- A list that the standard builds by appending is built here from its first item on.

What is decided where the standard leaves a choice, or asks for what a list of tokens has not.

- *Valid in the current context.* The standard says that it "intentionally does not specify how
  sufficient context should be passed around to enable validity-checking". There is no context
  here: every rule and every declaration is valid. So `consume an at-rule` always returns its
  rule, `consume a qualified rule` never returns an invalid rule error, and what a property
  admits is a later check on the tree. A declaration is still refused where step 8 of `consume a
  declaration` refuses it by its shape, and that is what sends `a:hover { }` inside a block to be
  read as a rule.
- *Parse errors* are not values. The functions return what the standard says is returned, and a
  docstring names the places where the standard flags a parse error.
- *The original text of a custom property* (step 8 of `consume a declaration`) is not kept:
  `Declaration` has no field for it, and a list of tokens has no source text. Its value is the
  component values, as for any declaration.
- *The `unicode-range` descriptor* (the same step) is not read again. The standard tokenizes the
  source text of its value a second time with unicode ranges allowed, and a list of tokens no
  longer has that text. The value of a declaration named `unicode-range` is the component values
  of the tokens given, as for any declaration.
- *The end of a block's contents.* The sealed text returns `rules` at the end of the input and at
  a right curly bracket, and says nothing of the declarations it holds in `decls` at that moment.
  Read by the letter, `a { color: red }` has no declaration. Here those declarations are the last
  item of the result (`consumeBlockContents`).
- *A custom property name string* has no definition in the sealed files. It is read as a name
  that starts with two hyphen-minus, which is what `consume a qualified rule` asks of a prelude
  and what CSS Variables says of a custom property.

How the tree holds a block. `consume a block's contents` gives rules and lists of declarations in
the order they stand. A list of declarations is the rule `Rule.nested` in that result. For a
qualified rule the standard takes a first list of declarations as the rule's declarations and
keeps each later list as a nested declarations rule among the child rules; `Rule.splitBlock` does
that. For an at-rule the standard assigns the whole result to the child rules and leaves to each
rule what its lists of declarations become. Here an at-rule's block is split the same way as a
qualified rule's, so `@font-face { ... }` has declarations and `@media { ... }` has child rules.
Nothing is lost: a list of declarations in the result is never empty, so a block whose child
rules open with `Rule.nested` is never returned, and the split has an inverse.

What this module does not claim: that a browser parses so, or that a tree it returns is valid
CSS. The laws are in `Whatwg/Css/Syntax/Parse/Laws.lean`: the parser reads back the tree that
`Whatwg/Css/Syntax/Write.lean` wrote.
-/

namespace Whatwg.Css.Syntax

/-! ## Token streams (`parser-definitions`) -/

/-- "Discard whitespace": while the next token is a whitespace token, discard a token. -/
def discardWhitespace : List Token → List Token
  | .whitespace :: rest => discardWhitespace rest
  | input => input

theorem discardWhitespace_length_le (input : List Token) :
    (discardWhitespace input).length ≤ input.length := by
  fun_induction discardWhitespace input with
  | case1 rest ih => exact Nat.le_succ_of_le ih
  | case2 input _ => exact Nat.le_refl _

/-- The name of an at-keyword token. -/
def Token.atKeyword? : Token → Option (List Char)
  | .atKeyword name => some name
  | _ => none

/-- A result and the tokens after it, which are no more than the tokens given. The algorithms
that call each other return this, so that Lean sees each of them end. -/
abbrev Consumed (α : Type) (input : List Token) : Type :=
  { p : α × List Token // p.2.length ≤ input.length }

/-! ## Component values -/

mutual

/-- `consume-component-value` with the next token in hand: see `consumeComponentValue`. -/
def consumeComponentValueSized (token : Token) (rest : List Token) : Consumed Component rest :=
  match token with
  | .openCurly => consumeSimpleBlockSized .curly rest
  | .openSquare => consumeSimpleBlockSized .square rest
  | .openParen => consumeSimpleBlockSized .paren rest
  | .function name => consumeFunctionSized name rest
  | token => ⟨(.token token, rest), Nat.le_refl _⟩
termination_by 3 * rest.length + 3

/-- `consume-simple-block` after its opening token: see `consumeSimpleBlock`. -/
def consumeSimpleBlockSized (bracket : Bracket) (input : List Token) : Consumed Component input :=
  let value := consumeUntilSized (· == bracket.closing) input
  ⟨(.block bracket value.val.1, value.val.2.drop 1),
    Nat.le_trans (Nat.le_of_eq List.length_drop) (Nat.le_trans (Nat.sub_le _ _) value.property)⟩
termination_by 3 * input.length + 2

/-- `consume-function` after its function token: see `consumeFunction`. -/
def consumeFunctionSized (name : List Char) (input : List Token) : Consumed Component input :=
  let value := consumeUntilSized (· == .closeParen) input
  ⟨(.function name value.val.1, value.val.2.drop 1),
    Nat.le_trans (Nat.le_of_eq List.length_drop) (Nat.le_trans (Nat.sub_le _ _) value.property)⟩
termination_by 3 * input.length + 2

/-- The loop that gathers component values: see `consumeUntil`. -/
def consumeUntilSized (ends : Token → Bool) (input : List Token) :
    Consumed (List Component) input :=
  match input with
  | [] => ⟨([], []), Nat.le_refl _⟩
  | token :: rest =>
    if ends token then ⟨([], token :: rest), Nat.le_refl _⟩
    else
      let value := consumeComponentValueSized token rest
      have h : (consumeComponentValueSized token rest).val.2.length ≤ rest.length :=
        (consumeComponentValueSized token rest).property
      let more := consumeUntilSized ends value.val.2
      ⟨(value.val.1 :: more.val.1, more.val.2),
        Nat.le_trans more.property (Nat.le_trans h (Nat.le_succ _))⟩
termination_by 3 * input.length + 1

end

/-- **The loop that gathers component values.** While the next token is not one that `ends` the
loop, and the input has not ended: consume a component value and append it. The token that ends
the loop is left in the input.

This is the `process` of five algorithms. `consume a list of component values` and the preludes
of `consume a qualified rule` and `consume an at-rule` say which tokens end it (`endsList`,
`endsPrelude`). In `consume a simple block` and `consume a function` the ending token ends it.
In all five a token that does not end the loop is handled by "consume a component value", or by
"consume a token and append the result" for a right curly bracket, which gives the same
component value. -/
def consumeUntil (ends : Token → Bool) (input : List Token) : List Component × List Token :=
  (consumeUntilSized ends input).val

/-- `consume-component-value`: consume a component value. `none` at the end of the input, where
the standard would return the EOF token; no algorithm of the standard calls it there.

- a left curly bracket, a left square bracket, a left parenthesis: consume a simple block;
- a function token: consume a function;
- anything else: the token, which is a preserved token. -/
def consumeComponentValue : List Token → Option (Component × List Token)
  | [] => none
  | token :: rest => some (consumeComponentValueSized token rest).val

/-- `consume-simple-block`: consume a simple block. The standard asserts that the next token
opens a block: here it is the argument `bracket`, and `input` is what follows it. "Let ending
token be the mirror variant of the next token" is `bracket.closing`. Component values are
consumed up to the ending token or the end of the input, and one token is then discarded. -/
def consumeSimpleBlock (bracket : Bracket) (input : List Token) : Component × List Token :=
  (consumeSimpleBlockSized bracket input).val

/-- `consume-function`: consume a function. The standard asserts that the next token is a
function token: here its value is the argument `name`, and `input` is what follows it. Component
values are consumed up to a right parenthesis or the end of the input, and one token is then
discarded. -/
def consumeFunction (name : List Char) (input : List Token) : Component × List Token :=
  (consumeFunctionSized name input).val

theorem consumeUntil_length_le (ends : Token → Bool) (input : List Token) :
    (consumeUntil ends input).2.length ≤ input.length :=
  (consumeUntilSized ends input).property

/-- The loop at the end of the input gathers nothing. -/
theorem consumeUntil_nil (ends : Token → Bool) : consumeUntil ends [] = ([], []) := by
  unfold consumeUntil
  rw [consumeUntilSized]

/-- The loop at a token that ends it gathers nothing and leaves the token. -/
theorem consumeUntil_of_ends {ends : Token → Bool} {token : Token} (rest : List Token)
    (h : ends token = true) : consumeUntil ends (token :: rest) = ([], token :: rest) := by
  unfold consumeUntil
  rw [consumeUntilSized, if_pos h]

/-- The loop at a token that does not end it takes that token: what is left is shorter. -/
theorem consumeUntil_length_lt {ends : Token → Bool} {token : Token} (rest : List Token)
    (h : ends token = false) :
    (consumeUntil ends (token :: rest)).2.length < (token :: rest).length := by
  unfold consumeUntil
  rw [consumeUntilSized, if_neg (by rw [h]; exact Bool.false_ne_true)]
  exact Nat.lt_succ_of_le (Nat.le_trans (consumeUntilSized ends _).property
    (consumeComponentValueSized token rest).property)

/-! ## Lists of component values and declarations -/

/-- Whether a token ends a list of component values: the stop token where one is passed, and a
right curly bracket where `nested` is true. -/
def endsList (stop : Option Token) (nested : Bool) (token : Token) : Bool :=
  stop.any (· == token) || (nested && token == .closeCurly)

/-- `consume-list-of-components`: consume a list of component values, given an optional stop
token and an optional `nested` (default false).

- the end of the input, the stop token: return the values;
- a right curly bracket: where `nested` is true, return the values; otherwise this is a parse
  error, and the token is appended to the values;
- anything else: consume a component value and append it. -/
def consumeListOfComponentValues (stop : Option Token := none) (nested : Bool := false)
    (input : List Token) : List Component × List Token :=
  consumeUntil (endsList stop nested) input

/-- `consume-declaration`, "consume the remnants of a bad declaration", given `nested`.

- the end of the input, a semicolon: discard a token and return;
- a right curly bracket: where `nested` is true, return; otherwise discard a token;
- anything else: consume a component value, and do nothing with it.

This is `consume a list of component values` with a semicolon as the stop token and the values
dropped, and then the semicolon discarded where it is the next token. -/
def consumeRemnantsOfBadDeclaration (nested : Bool) (input : List Token) : List Token :=
  match (consumeListOfComponentValues (some .semicolon) nested input).2 with
  | .semicolon :: rest => rest
  | rest => rest

theorem consumeRemnantsOfBadDeclaration_length_le (nested : Bool) (input : List Token) :
    (consumeRemnantsOfBadDeclaration nested input).length ≤ input.length := by
  have h := consumeUntil_length_le (endsList (some .semicolon) nested) input
  unfold consumeRemnantsOfBadDeclaration consumeListOfComponentValues
  split
  · rename_i rest heq
    rw [heq] at h
    exact Nat.le_of_succ_le h
  · exact h

/-- The remnants of a bad declaration take a token, but for a right curly bracket in a block. -/
theorem consumeRemnantsOfBadDeclaration_length_lt (nested : Bool) (token : Token)
    (rest : List Token) (h : nested = false ∨ token ≠ .closeCurly) :
    (consumeRemnantsOfBadDeclaration nested (token :: rest)).length < (token :: rest).length := by
  by_cases hs : token = .semicolon
  · subst hs
    have hends : endsList (some .semicolon) nested .semicolon = true := by
      simp only [endsList, Option.any_some, beq_self_eq_true, Bool.true_or]
    unfold consumeRemnantsOfBadDeclaration consumeListOfComponentValues
    rw [consumeUntil_of_ends rest hends]
    exact Nat.lt_succ_self _
  · have hends : endsList (some .semicolon) nested token = false := by
      have hne : (Token.semicolon == token) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun heq => hs heq.symm
      simp only [endsList, Option.any_some, hne, Bool.false_or, Bool.and_eq_false_imp,
        beq_eq_false_iff_ne]
      intro hn
      rcases h with h | h
      · rw [h] at hn
        exact absurd hn Bool.false_ne_true
      · exact h
    have hlt := consumeUntil_length_lt rest hends
    have hle := consumeRemnantsOfBadDeclaration_length_le nested (token :: rest)
    unfold consumeRemnantsOfBadDeclaration consumeListOfComponentValues at hle ⊢
    split
    · rename_i tail heq
      rw [heq] at hlt
      exact Nat.lt_of_succ_lt hlt
    · exact hlt

/-- Whether a component value is a whitespace token. -/
def Component.isWhitespace : Component → Bool
  | .token .whitespace => true
  | _ => false

/-- Whether a component value is a simple block whose associated token is a left curly
bracket. -/
def Component.isCurlyBlock : Component → Bool
  | .block .curly _ => true
  | _ => false

/-- Whether a name is an ASCII case-insensitive match for "important". -/
def isImportant (name : List Char) : Bool := name.map Char.toLower == "important".toList

/-- Whether a name starts with two hyphen-minus: the name of a custom property. The sealed files
do not define the standard's "custom property name string"; this is the reading taken. -/
def isCustomPropertyName : List Char → Bool
  | '-' :: '-' :: _ => true
  | _ => false

/-- Whether a value, read from its last non-whitespace item backwards, opens with an ident token
that matches "important" and then, after white space, a delim token with the value "!". Where it
does: the white space between the two, and what stands before the "!", both read backwards. -/
def importantSuffix : List Component → Option (List Component × List Component)
  | .token (.ident name) :: before =>
    match before.dropWhile Component.isWhitespace with
    | .token (.delim c) :: front =>
      if c = '!' ∧ isImportant name = true then
        some (before.takeWhile Component.isWhitespace, front)
      else none
    | _ => none
  | _ => none

/-- Step 6 of `consume-declaration`: "If the last two non-whitespace tokens in decl's value are
a delim token with the value "!" followed by an ident token with a value that is an ASCII
case-insensitive match for "important", remove them from decl's value and set decl's important
flag." The value with the two removed, and the flag. White space that stood around them stays,
and step 7 removes it. -/
def takeImportant (value : List Component) : List Component × Bool :=
  match importantSuffix (value.reverse.dropWhile Component.isWhitespace) with
  | some (between, front) =>
    (front.reverse ++ (between.reverse ++
      (value.reverse.takeWhile Component.isWhitespace).reverse), true)
  | none => (value, false)

/-- Step 7 of `consume-declaration`: "While the last item in decl's value is a whitespace token,
remove that token." -/
def dropTrailingWhitespace (value : List Component) : List Component :=
  (value.reverse.dropWhile Component.isWhitespace).reverse

/-- The test of step 8 of `consume-declaration`: the value "contains a top-level simple block
with an associated token of a left curly bracket, and also contains any other non-whitespace
value". -/
def blockAmongOthers (value : List Component) : Bool :=
  (value.filter fun c => !c.isWhitespace).any Component.isCurlyBlock &&
    decide (2 ≤ (value.filter fun c => !c.isWhitespace).length)

/-- `consume-declaration`: consume a declaration, given `nested` (default false). `none` where
the standard returns nothing.

1. The next token is an ident token: consume it, and it is the name. Otherwise consume the
   remnants of a bad declaration and return nothing.
2. Discard whitespace.
3. The next token is a colon: discard it. Otherwise consume the remnants of a bad declaration
   and return nothing.
4. Discard whitespace.
5. Consume a list of component values, with `nested` and a semicolon as the stop token: the
   value.
6. `takeImportant`.
7. `dropTrailingWhitespace`.
8. A name of a custom property: the standard keeps the original text, and this model does not.
   "Otherwise, if decl's value contains a top-level simple block with an associated token of a
   left curly bracket, and also contains any other non-whitespace value, return nothing." The
   third case, a name that matches "unicode-range", is not modelled: the value stays as it is.
9. "If decl is valid in the current context, return it": there is no context, and it is
   returned.

The semicolon that ends a declaration is left in the input. -/
def consumeDeclaration (nested : Bool := false) (input : List Token) :
    Option Declaration × List Token :=
  match input with
  | .ident name :: rest =>
    match discardWhitespace rest with
    | .colon :: afterColon =>
      let value :=
        consumeListOfComponentValues (some .semicolon) nested (discardWhitespace afterColon)
      let flagged := takeImportant value.1
      let trimmed := dropTrailingWhitespace flagged.1
      (if isCustomPropertyName name = false ∧ blockAmongOthers trimmed = true then none
        else some { name := name, value := trimmed, important := flagged.2 },
        value.2)
    | other => (none, consumeRemnantsOfBadDeclaration nested other)
  | other => (none, consumeRemnantsOfBadDeclaration nested other)

/-- A declaration takes a token, but where it is asked for at a right curly bracket in a block.
So the loops that read declarations end. -/
theorem consumeDeclaration_length_lt (nested : Bool) (token : Token) (rest : List Token)
    (h : nested = false ∨ token ≠ .closeCurly) :
    (consumeDeclaration nested (token :: rest)).2.length < (token :: rest).length := by
  unfold consumeDeclaration
  split
  · rename_i name tail heq
    cases heq
    have h₁ := discardWhitespace_length_le rest
    split
    · rename_i afterColon heq
      rw [heq] at h₁
      have h₂ := discardWhitespace_length_le afterColon
      have h₃ := consumeUntil_length_le (endsList (some .semicolon) nested)
        (discardWhitespace afterColon)
      simp only [consumeListOfComponentValues, List.length_cons] at h₁ ⊢
      omega
    · have h₂ := consumeRemnantsOfBadDeclaration_length_le nested (discardWhitespace rest)
      simp only [List.length_cons]
      omega
  · exact consumeRemnantsOfBadDeclaration_length_lt nested token rest h

/-! ## Rules -/

/-- Whether a token ends the prelude of a rule: a left curly bracket, and the tokens that end a
list of component values. The prelude of an at-rule ends as that of a qualified rule whose stop
token is a semicolon. -/
def endsPrelude (stop : Option Token) (nested : Bool) (token : Token) : Bool :=
  token == .openCurly || endsList stop nested token

/-- The test of `consume-qualified-rule` at a left curly bracket: "the first two non-whitespace
values of rule's prelude are an ident token whose value starts with "--" followed by a colon
token". -/
def startsAsCustomProperty (prelude : List Component) : Bool :=
  match prelude.filter fun c => !c.isWhitespace with
  | .token (.ident name) :: .token .colon :: _ => isCustomPropertyName name
  | _ => false

namespace Rule

/-- A declaration before what follows it in a block: it joins the list of declarations that
follows it, or starts one. The standard gathers declarations in `decls` and appends that list to
`rules` when a rule comes; so declarations that stand together are one item of the result. -/
def consDeclaration (d : Declaration) : List Rule → List Rule
  | .nested declarations :: rules => .nested (d :: declarations) :: rules
  | rules => .nested [d] :: rules

/-- The declarations and the child rules of a block's contents, as `consume-qualified-rule`
says: "If the first item of child rules is a list of declarations, remove it from child rules
and assign it to rule's declarations." Each later list of declarations is already the nested
declarations rule that the standard replaces it with. -/
def splitBlock : List Rule → List Declaration × List Rule
  | .nested declarations :: rules => (declarations, rules)
  | rules => ([], rules)

end Rule

/-- What is left after the token that follows a prelude is shorter than the input. -/
theorem length_lt_of_after {after input rest : List Token} {token : Token}
    (h : after = token :: rest) (hle : after.length ≤ input.length) :
    rest.length < input.length := by
  subst h
  exact hle

/-- A prelude that a token other than a left curly bracket ends took a token, where the input
did not open with a token that ends a list. -/
theorem prelude_length_lt {stop : Option Token} {nested : Bool} {input rest : List Token}
    {token : Token} (h : (consumeUntil (endsPrelude stop nested) input).2 = token :: rest)
    (ht : token ≠ .openCurly) (first : Token) (tail : List Token) (hi : input = first :: tail)
    (hf : endsList stop nested first = false) : (token :: rest).length < input.length := by
  subst hi
  cases hp : endsPrelude stop nested first with
  | false =>
    have := consumeUntil_length_lt tail hp
    rw [h] at this
    exact this
  | true =>
    rw [consumeUntil_of_ends tail hp] at h
    cases h
    simp only [endsPrelude, hf, Bool.or_false, beq_iff_eq] at hp
    exact absurd hp ht

mutual

/-- `consume-at-rule` after its at-keyword token: see `consumeAtRule`. -/
def consumeAtRuleSized (name : List Char) (nested : Bool) (input : List Token) :
    Consumed Rule input :=
  match h : (consumeUntil (endsPrelude (some .semicolon) nested) input).2 with
  | [] =>
    ⟨(.statement name (consumeUntil (endsPrelude (some .semicolon) nested) input).1, []),
      Nat.zero_le _⟩
  | token :: rest =>
    have hlt : rest.length < input.length :=
      length_lt_of_after h (consumeUntil_length_le _ input)
    if token = .semicolon then
      ⟨(.statement name (consumeUntil (endsPrelude (some .semicolon) nested) input).1, rest),
        Nat.le_of_lt hlt⟩
    else if token = .openCurly then
      let block := consumeBlockSized rest
      ⟨(.blockAt name (consumeUntil (endsPrelude (some .semicolon) nested) input).1
          (Rule.splitBlock block.val.1).1 (Rule.splitBlock block.val.1).2, block.val.2),
        Nat.le_trans block.property (Nat.le_of_lt hlt)⟩
    else
      ⟨(.statement name (consumeUntil (endsPrelude (some .semicolon) nested) input).1,
          token :: rest), hlt⟩
termination_by 3 * input.length

/-- `consume-qualified-rule`: see `consumeQualifiedRule`. What is left is shorter than the input
where the input does not open with a token at which the standard returns nothing at once. -/
def consumeQualifiedRuleSized (stop : Option Token) (nested : Bool) (input : List Token) :
    { p : Option Rule × List Token // p.2.length ≤ input.length ∧
      ∀ first tail, input = first :: tail → endsList stop nested first = false →
        p.2.length < input.length } :=
  match h : (consumeUntil (endsPrelude stop nested) input).2 with
  | [] => ⟨(none, []), Nat.zero_le _, fun _ _ hi _ => hi ▸ Nat.zero_lt_succ _⟩
  | token :: rest =>
    have hlt : rest.length < input.length :=
      length_lt_of_after h (consumeUntil_length_le _ input)
    if ht : token = .openCurly then
      if startsAsCustomProperty (consumeUntil (endsPrelude stop nested) input).1 = true then
        if nested = true then
          have hr : (consumeRemnantsOfBadDeclaration true (token :: rest)).length <
              input.length :=
            Nat.lt_of_lt_of_le
              (consumeRemnantsOfBadDeclaration_length_lt true token rest
                (Or.inr (ht ▸ Token.noConfusion)))
              (h ▸ consumeUntil_length_le _ input)
          ⟨(none, consumeRemnantsOfBadDeclaration true (token :: rest)), Nat.le_of_lt hr,
            fun _ _ _ _ => hr⟩
        else
          let block := consumeBlockSized rest
          ⟨(none, block.val.2), Nat.le_trans block.property (Nat.le_of_lt hlt),
            fun _ _ _ _ => Nat.lt_of_le_of_lt block.property hlt⟩
      else
        let block := consumeBlockSized rest
        ⟨(some (.qualified (consumeUntil (endsPrelude stop nested) input).1
            (Rule.splitBlock block.val.1).1 (Rule.splitBlock block.val.1).2), block.val.2),
          Nat.le_trans block.property (Nat.le_of_lt hlt),
          fun _ _ _ _ => Nat.lt_of_le_of_lt block.property hlt⟩
    else
      ⟨(none, token :: rest), h ▸ consumeUntil_length_le _ input,
        fun first tail hi hf => prelude_length_lt h ht first tail hi hf⟩
termination_by 3 * input.length

/-- `consume-block` after its left curly bracket: see `consumeBlock`. -/
def consumeBlockSized (input : List Token) : Consumed (List Rule) input :=
  let contents := consumeBlockContentsSized input
  ⟨(contents.val.1, contents.val.2.drop 1),
    Nat.le_trans (Nat.le_of_eq List.length_drop) (Nat.le_trans (Nat.sub_le _ _) contents.property)⟩
termination_by 3 * input.length + 2

/-- `consume-block-contents`: see `consumeBlockContents`. -/
def consumeBlockContentsSized (input : List Token) : Consumed (List Rule) input :=
  match input with
  | [] => ⟨([], []), Nat.le_refl _⟩
  | token :: rest =>
    if hs : token = .whitespace ∨ token = .semicolon then
      let more := consumeBlockContentsSized rest
      ⟨more.val, Nat.le_succ_of_le more.property⟩
    else if hc : token = .closeCurly then ⟨([], token :: rest), Nat.le_refl _⟩
    else
      match token.atKeyword? with
      | some name =>
        let rule := consumeAtRuleSized name true rest
        have h : (consumeAtRuleSized name true rest).val.2.length ≤ rest.length :=
          (consumeAtRuleSized name true rest).property
        let more := consumeBlockContentsSized rule.val.2
        ⟨(rule.val.1 :: more.val.1, more.val.2),
          Nat.le_trans more.property (Nat.le_succ_of_le h)⟩
      | none =>
        match (consumeDeclaration true (token :: rest)).1 with
        | some declaration =>
          have h : (consumeDeclaration true (token :: rest)).2.length < (token :: rest).length :=
            consumeDeclaration_length_lt true token rest (Or.inr hc)
          let more := consumeBlockContentsSized (consumeDeclaration true (token :: rest)).2
          ⟨(Rule.consDeclaration declaration more.val.1, more.val.2),
            Nat.le_trans more.property (Nat.le_of_lt h)⟩
        | none =>
          let rule := consumeQualifiedRuleSized (some .semicolon) true (token :: rest)
          have h : (consumeQualifiedRuleSized (some .semicolon) true (token :: rest)).val.2.length <
              (token :: rest).length :=
            (consumeQualifiedRuleSized (some .semicolon) true (token :: rest)).property.2 token rest
              rfl (by
                have h₁ : (Token.semicolon == token) = false :=
                  beq_eq_false_iff_ne.mpr fun heq => hs (Or.inr heq.symm)
                have h₂ : (token == Token.closeCurly) = false := beq_eq_false_iff_ne.mpr hc
                simp only [endsList, Option.any_some, h₁, h₂, Bool.and_false, Bool.or_self])
          let more := consumeBlockContentsSized rule.val.2
          ⟨(rule.val.1.toList ++ more.val.1, more.val.2),
            Nat.le_trans more.property (Nat.le_of_lt h)⟩
termination_by 3 * input.length + 1

end

/-- `consume-at-rule`: consume an at-rule, given `nested` (default false). The standard asserts
that the next token is an at-keyword token: here its value is the argument `name`, and `input`
is what follows it.

Component values are consumed into the prelude up to the token that ends it, and then:

- a semicolon, the end of the input: discard a token; a statement at-rule;
- a right curly bracket, where `nested` is true: a statement at-rule, and the token stays. (Where
  `nested` is false the token is appended to the prelude, and does not end it.)
- a left curly bracket: consume a block, "and assign the result to rule's child rules"; a block
  at-rule, its block split by `Rule.splitBlock`.

"If rule is valid in the current context, return it": there is no context, and the rule is always
returned. -/
def consumeAtRule (name : List Char) (nested : Bool := false) (input : List Token) :
    Rule × List Token :=
  (consumeAtRuleSized name nested input).val

/-- `consume-qualified-rule`: consume a qualified rule, given an optional stop token and
`nested` (default false). `none` where the standard returns nothing.

Component values are consumed into the prelude up to the token that ends it, and then:

- the end of the input, the stop token: a parse error; return nothing. The stop token stays.
- a right curly bracket, where `nested` is true: a parse error; return nothing. The token stays.
  (Where `nested` is false the token is appended to the prelude, and does not end it.)
- a left curly bracket: where the prelude starts as a custom property does
  (`startsAsCustomProperty`), consume the remnants of a bad declaration if `nested` is true, and
  consume a block if it is false, and return nothing. Otherwise consume a block; the rule has the
  prelude and the block, split by `Rule.splitBlock`.

"If rule is valid in the current context, return it; otherwise return an invalid rule error":
there is no context, so the rule is returned and no invalid rule error arises. -/
def consumeQualifiedRule (stop : Option Token := none) (nested : Bool := false)
    (input : List Token) : Option Rule × List Token :=
  (consumeQualifiedRuleSized stop nested input).val

/-- `consume-block`: consume a block. The standard asserts that the next token is a left curly
bracket and discards it: here `input` is what follows it. "Consume a block's contents from input
and let rules be the result. Discard a token from input." -/
def consumeBlock (input : List Token) : List Rule × List Token :=
  (consumeBlockSized input).val

/-- `consume-block-contents`: consume a block's contents. The result is rules and lists of
declarations in the order they stand; a list of declarations is a `Rule.nested`.

- a whitespace token, a semicolon: discard a token;
- the end of the input, a right curly bracket: return. The sealed text says "Return rules" and no
  more. Here the declarations gathered since the last rule are returned too, as the last item:
  read by the letter, the declarations at the end of every block would be lost.
- an at-keyword token: consume an at-rule with `nested` set to true, and append it;
- anything else: consume a declaration with `nested` set to true. Where one is returned it joins
  the declarations (`Rule.consDeclaration`). Otherwise the same tokens are read again: consume a
  qualified rule with `nested` set to true and a semicolon as the stop token, and append the rule
  where one is returned. Where nothing is returned, nothing is done: declarations on the two
  sides of what was dropped stay one list.

The right curly bracket that ends a block is left in the input. -/
def consumeBlockContents (input : List Token) : List Rule × List Token :=
  (consumeBlockContentsSized input).val

theorem consumeAtRule_length_le (name : List Char) (nested : Bool) (input : List Token) :
    (consumeAtRule name nested input).2.length ≤ input.length :=
  (consumeAtRuleSized name nested input).property

theorem consumeQualifiedRule_length_le (stop : Option Token) (nested : Bool)
    (input : List Token) : (consumeQualifiedRule stop nested input).2.length ≤ input.length :=
  (consumeQualifiedRuleSized stop nested input).property.1

/-- A qualified rule at the top level takes a token: so a stylesheet's contents end. -/
theorem consumeQualifiedRule_length_lt (token : Token) (rest : List Token) :
    (consumeQualifiedRule none false (token :: rest)).2.length < (token :: rest).length :=
  (consumeQualifiedRuleSized none false (token :: rest)).property.2 token rest rfl rfl

/-- `consume-stylesheet-contents`: consume a stylesheet's contents.

- a whitespace token, a CDO token, a CDC token: discard a token;
- the end of the input: return the rules;
- an at-keyword token: consume an at-rule, and append it;
- anything else: consume a qualified rule, and append it where a rule is returned. -/
def consumeStylesheetContents (input : List Token) : List Rule :=
  match input with
  | [] => []
  | token :: rest =>
    if token = .whitespace ∨ token = .cdo ∨ token = .cdc then consumeStylesheetContents rest
    else
      match token.atKeyword? with
      | some name =>
        (consumeAtRule name false rest).1 ::
          consumeStylesheetContents (consumeAtRule name false rest).2
      | none =>
        (consumeQualifiedRule none false (token :: rest)).1.toList ++
          consumeStylesheetContents (consumeQualifiedRule none false (token :: rest)).2
termination_by input.length
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (consumeAtRule_length_le name false rest)
  · exact consumeQualifiedRule_length_lt token rest

/-- `consume-style-attribute`: consume a style attribute. The result is one list of
declarations.

- a whitespace token, a semicolon: discard a token;
- the end of the input: return the declarations;
- an at-keyword token: consume an at-rule, and ignore the result;
- anything else: consume a declaration, and append it where one is returned. -/
def consumeStyleAttribute (input : List Token) : List Declaration :=
  match input with
  | [] => []
  | token :: rest =>
    if token = .whitespace ∨ token = .semicolon then consumeStyleAttribute rest
    else
      match token.atKeyword? with
      | some name => consumeStyleAttribute (consumeAtRule name false rest).2
      | none =>
        (consumeDeclaration false (token :: rest)).1.toList ++
          consumeStyleAttribute (consumeDeclaration false (token :: rest)).2
termination_by input.length
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (consumeAtRule_length_le name false rest)
  · exact consumeDeclaration_length_lt false token rest (Or.inl rfl)

/-! ## Parser entry points (`parser-entry-points`)

Each takes a list of tokens: the standard's "normalize into a token stream" of a list of tokens.
The forms that end in `Text` normalize a string: filter code points, then tokenize
(`tokenizeText`). Where the standard returns an error in place of a result, the function returns
`none`. -/

/-- `parse-stylesheet`: parse a stylesheet. A stylesheet's location is not modelled. -/
def parseStylesheet (input : List Token) : Stylesheet := ⟨consumeStylesheetContents input⟩

/-- `parse-stylesheet-contents`: parse a stylesheet's contents. -/
def parseStylesheetContents (input : List Token) : List Rule := consumeStylesheetContents input

/-- `parse-block-contents`: parse a block's contents. As the standard has it, a right curly
bracket at the top ends the reading, and what follows it is not read. -/
def parseBlockContents (input : List Token) : List Rule := (consumeBlockContents input).1

/-- `parse-style-attribute`: parse a style attribute. -/
def parseStyleAttribute (input : List Token) : List Declaration := consumeStyleAttribute input

/-- `parse-rule`: parse a rule. Discard whitespace; at the end of the input, an error; at an
at-keyword token consume an at-rule, and otherwise consume a qualified rule, where nothing
returned is an error; discard whitespace; the rule where the input has ended, and an error
otherwise. -/
def parseRule (input : List Token) : Option Rule :=
  match discardWhitespace input with
  | [] => none
  | token :: rest =>
    let result : Option Rule × List Token :=
      match token.atKeyword? with
      | some name => (some (consumeAtRule name false rest).1, (consumeAtRule name false rest).2)
      | none => consumeQualifiedRule none false (token :: rest)
    if (discardWhitespace result.2).isEmpty then result.1 else none

/-- `parse-declaration`: parse a declaration. Discard whitespace; consume a declaration; an
error where nothing is returned. As the standard has it, what follows the declaration is not
looked at. -/
def parseDeclaration (input : List Token) : Option Declaration :=
  (consumeDeclaration false (discardWhitespace input)).1

/-- `parse-component-value`: parse a component value. Discard whitespace; at the end of the
input, an error; consume a component value; discard whitespace; the value where the input has
ended, and an error otherwise. -/
def parseComponentValue (input : List Token) : Option Component :=
  match consumeComponentValue (discardWhitespace input) with
  | none => none
  | some (value, rest) => if (discardWhitespace rest).isEmpty then some value else none

/-- `parse-list-of-component-values`: parse a list of component values. -/
def parseComponentValues (tokens : List Token) : List Component :=
  (consumeListOfComponentValues none false tokens).1

/-- `parse-comma-separated-list-of-component-values`: parse a comma-separated list of component
values. While the input has not ended: consume a list of component values with a comma as the
stop token, append it to the groups, and discard a token. So a comma at the end of the input
gives no empty group after it. -/
def parseCommaSeparatedComponentValues (input : List Token) : List (List Component) :=
  match input with
  | [] => []
  | token :: rest =>
    (consumeListOfComponentValues (some .comma) false (token :: rest)).1 ::
      parseCommaSeparatedComponentValues
        ((consumeListOfComponentValues (some .comma) false (token :: rest)).2.drop 1)
termination_by input.length
decreasing_by
  have h := consumeUntil_length_le (endsList (some .comma) false) (token :: rest)
  simp only [consumeListOfComponentValues, List.length_drop, List.length_cons] at h ⊢
  omega

/-- The stylesheet of a text. -/
def parseStylesheetText (text : String) : Stylesheet := parseStylesheet (tokenizeText text)

/-- The rules and lists of declarations of the text of a block's contents. -/
def parseBlockContentsText (text : String) : List Rule := parseBlockContents (tokenizeText text)

/-- The declarations of the text of a `style` attribute. -/
def parseStyleAttributeText (text : String) : List Declaration :=
  parseStyleAttribute (tokenizeText text)

/-- The rule of a text, where the text is one rule. -/
def parseRuleText (text : String) : Option Rule := parseRule (tokenizeText text)

/-- The declaration of a text, where the text opens with one. -/
def parseDeclarationText (text : String) : Option Declaration :=
  parseDeclaration (tokenizeText text)

/-- The component value of a text, where the text is one. -/
def parseComponentValueText (text : String) : Option Component :=
  parseComponentValue (tokenizeText text)

/-- The component values of a text. -/
def parseComponentValuesText (text : String) : List Component :=
  parseComponentValues (tokenizeText text)

/-- The groups of component values of a text, split at its commas. -/
def parseCommaSeparatedComponentValuesText (text : String) : List (List Component) :=
  parseCommaSeparatedComponentValues (tokenizeText text)

end Whatwg.Css.Syntax
