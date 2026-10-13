import Whatwg.Css.Values.Definition
import Whatwg.Css.Syntax.Tree

/-!
# Whatwg.Css.Values.Admits

Owner: the meaning of a definition in the Value Definition Syntax (slice K3 of
`docs/CSS-PACKAGE-PLAN.md`; ruling CS-5): which values it admits.

The authority is CSS Values and Units Module Level 4, sealed at
`vendor/w3c-csswg-drafts-50337328/css-values-4/Overview.bs`: the section `value-defs` for the
combinators, the multipliers, the comma that may be left out (`comb-comma`) and white space
(`component-whitespace`), and the sections named beside each basic type.

- `admits env d value`: the definition admits the value. A value is a list of component values
  (`Whatwg/Css/Syntax/Tree.lean`), as the parser of CSS Syntax 3 gives one.
- `Env`: what a name in angle brackets stands for: another definition, or a basic type, which
  is a test of one component value.
- `Language`: a set of values as its test. Each combinator and each multiplier is one function
  on languages, and it says what the standard's sentence says: a value is admitted where it
  can be cut into the pieces the sentence asks for. Nothing is consumed and nothing is left
  over, so a law of `Whatwg/Css/Values/Admits/Laws.lean` is close to its definition.
- `Basic`: the basic types this slice needs, each a reading of prose under its anchor.

How it ends on every input. The tree is walked by structural recursion. A name is unfolded at
most `depth` times on any path (the last argument of `admits`, 32 where none is given): past
that a name admits nothing. A repetition is tried up to the length of the value, since a
piece that is empty adds nothing. No environment and no value makes it run on.

What it costs. It searches: a juxtaposition takes every cut in turn, and `&&` and `||` take
every part at every cut. That is exponential in the worst case, and small where each part of a
combination takes few component values. `WhatwgTest/Css/Values.lean` holds the measure at the
sizes real properties have.

What this module does not claim:

- That a browser parses a value so. This is the grammar's judgment.
- The CSS-wide keywords. `component-types` says that every property also accepts them "as the
  sole component of their property value" and that "these are not listed explicitly". A
  definition is judged as it is written.
- Which derivation a parser takes. `custom-idents` says that "a `<custom-ident>` production
  can only claim the keyword if no other unfulfilled production can claim it". `admits` asks
  whether one derivation exists.
- White space that a grammar's prose makes significant. `component-whitespace` lets white
  space stand "before, after, and/or between components", and every white space token is
  dropped before a value is judged. The prose of `calc()` asks for it around `+` and `-`.
- A quoted bracket. `'['` never matches: a bracket of a value is a block, not a token.
- A range on a name that stands for a definition. It admits nothing.
-/

namespace Whatwg.Css.Values

open Whatwg.Css.Syntax (Component Token)

/-! ## Values -/

/-- A set of values, as its test. -/
abbrev Language : Type := List Component → Bool

/-- Two names are one, ASCII case-insensitively (`keywords`: "Keywords are identifiers and are
interpreted ASCII case-insensitively (i.e., [a-z] and [A-Z] are equivalent)"). -/
def sameName (a b : List Char) : Bool := a.map Char.toLower == b.map Char.toLower

/-- The component value is a white space token. -/
def isBlank : Component → Bool
  | .token .whitespace => true
  | _ => false

/-- A value with its white space dropped (`component-whitespace`): "white space and/or
comments may appear before, after, and/or between components combined using the above
combinators and multipliers". A comment is no token, so a value holds none. -/
def strip (v : List Component) : List Component := v.filter fun c => !isBlank c

/-- Every way to cut a list in two, the shortest first piece first. -/
def splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map fun s => (x :: s.1, s.2)

/-- Every way to take one member out of a list: the member, and the others in order. -/
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map fun p => (p.1, x :: p.2)

namespace Language

/-- Exactly one component value, which passes the test. -/
def just (test : Component → Bool) : Language
  | [c] => test c
  | _ => false

/-- Juxtaposition (`component-combinators`): "all of them must occur, in the given order".
The value is cut into one piece for each part. -/
def seq : List Language → Language
  | [], v => v.isEmpty
  | l :: ls, v => (splits v).any fun s => l s.1 && seq ls s.2

/-- A bar (`comb-one`): "exactly one of them must occur". -/
def oneOf (ls : List Language) : Language := fun v => ls.any fun l => l v

/-- A double ampersand (`comb-all`): "all of which must occur, in any order". Some part takes
a first piece, and the others take the rest. The number bounds the parts. -/
def allOf : Nat → List Language → Language
  | _, [], v => v.isEmpty
  | 0, _ :: _, _ => false
  | n + 1, l :: ls, v =>
    (picks (l :: ls)).any fun p => (splits v).any fun s => p.1 s.1 && allOf n p.2 s.2

/-- A double bar (`comb-any`): "one or more of them must occur, in any order". Some part takes
a first piece, and the rest is empty or taken by one or more of the others. -/
def anyOf : Nat → List Language → Language
  | 0, _, _ => false
  | n + 1, ls, v =>
    (picks ls).any fun p => (splits v).any fun s => p.1 s.1 && (s.2.isEmpty || anyOf n p.2 s.2)

/-- Zero or more pieces, each admitted and none empty. An empty piece adds nothing to a value,
so none is taken, and the number of pieces is at most the length of the value. -/
def many (l : Language) : Nat → Language
  | 0, v => v.isEmpty
  | n + 1, v => v.isEmpty || (splits v).any fun s => !s.1.isEmpty && l s.1 && many l n s.2

/-- A number of pieces between two bounds, each admitted (`mult-num`, `mult-num-range`). -/
def counted (l : Language) (lo hi : Nat) : Language := fun v =>
  (List.range (hi + 1)).any fun n => decide (lo ≤ n) && seq (List.replicate n l) v

/-- Exactly `n` pieces with one comma between two of them. -/
def listN (l : Language) : Nat → Language
  | 0, v => v.isEmpty
  | 1, v => l v
  | n + 2, v =>
    (splits v).any fun s => l s.1 && (match s.2 with
      | .token .comma :: w => listN l (n + 1) w
      | _ => false)

/-- One piece or more, at most `n`, with one comma between two of them (`mult-comma`): "occurs
one or more times, separated by comma tokens". -/
def listUpTo (l : Language) : Nat → Language
  | 0, _ => false
  | n + 1, v =>
    l v || (splits v).any fun s => l s.1 && (match s.2 with
      | .token .comma :: w => listUpTo l n w
      | _ => false)

/-- A number of pieces between two bounds, with one comma between two of them: `#{A,B}`. -/
def listCounted (l : Language) (lo hi : Nat) : Language := fun v =>
  (List.range (hi + 1)).any fun n => decide (lo ≤ n) && listN l n v

/-- The language of a part under a multiplier (`component-multipliers`). A repetition with no
upper bound is tried up to the length of the value. -/
def mult (l : Language) : Multiplier → Language
  | .star, v => many l v.length v
  | .plus, v => if v.isEmpty then l [] else many l v.length v
  | .opt, v => v.isEmpty || l v
  | .times (.exactly a), v => counted l a a v
  | .times (.between a b), v => counted l a b v
  | .times (.atLeast a), v => counted l a (max a v.length) v
  | .hash none, v => listUpTo l (v.length + 1) v
  | .hash (some (.exactly a)), v => listCounted l a a v
  | .hash (some (.between a b)), v => listCounted l a b v
  | .hash (some (.atLeast a)), v => listCounted l a (max a (v.length + 1)) v
  | .req, v => !v.isEmpty && l v

/-- A juxtaposition whose commas may be left out (`comb-comma`). A part is `none` for a comma
of the grammar, and a language otherwise.

"Within a top-level list in a property or other CSS value, or a function's argument list, a
comma specified in the grammar must be omitted if: all items preceding the comma have been
omitted; all items following the comma have been omitted; multiple commas would be adjacent
(ignoring white space/comments), due to the items between the commas being omitted."

An item is omitted where it takes nothing. `seen` says that an item before this point took
something, and `owed` that a comma of the grammar stands between that item and this point.
An item that takes something takes the owed comma first. A comma that is still owed at the
end is left out. -/
def args : List (Option Language) → Bool → Bool → Language
  | [], _, _, v => v.isEmpty
  | none :: ps, seen, _, v => args ps seen seen v
  | some l :: ps, seen, owed, v =>
    (l [] && args ps seen owed v) ||
      (if owed then
        (match v with
          | .token .comma :: w =>
            (splits w).any fun s => !s.1.isEmpty && l s.1 && args ps true false s.2
          | _ => false)
      else (splits v).any fun s => !s.1.isEmpty && l s.1 && args ps true false s.2)

end Language

/-! ## Names -/

/-- What a name in angle brackets stands for. -/
inductive Meaning where
  /-- Another definition: the right-hand side of a production. -/
  | production (d : Definition)
  /-- A basic type: a test of one component value, given the bracketed range of the use. -/
  | basic (test : Option Range → Component → Bool)

/-- What each name stands for. A name that the environment does not know admits nothing. -/
structure Env where
  /-- `<name>`. -/
  type : String → Option Meaning
  /-- `<name()>`: the definition of the function. -/
  function : String → Option Definition
  /-- `<'name'>`: the value grammar of the property. -/
  property : String → Option Definition

/-- The environment of three lists: the first entry of a name is the one. -/
def Env.ofLists (types : List (String × Meaning))
    (functions properties : List (String × Definition)) : Env where
  type := fun n => (types.find? fun e => e.1 == n).map fun e => e.2
  function := fun n => (functions.find? fun e => e.1 == n).map fun e => e.2
  property := fun n => (properties.find? fun e => e.1 == n).map fun e => e.2

/-- The grammar of a property as `<'name'>` stands for it (`component-types`, item 3): "if the
property's value grammar is a comma-separated repetition, the corresponding type does not
include the top-level comma-separated list multiplier." -/
def Definition.unlisted : Definition → Definition
  | .mult x (.hash _) => x
  | d => d

/-! ## A definition as a language -/

/-- The token a delimiter of a grammar stands for (`component-types`, item 6): "Delimiters,
which represent their corresponding tokens." A comma, a colon and a semicolon are tokens of
their own, and any other character is a delimiter token. -/
def isDelim (c : Char) : Component → Bool
  | .token .comma => c == ','
  | .token .colon => c == ':'
  | .token .semicolon => c == ';'
  | .token (.delim x) => x == c
  | _ => false

/-- The component value is an identifier of this name, ASCII case-insensitively. -/
def isKeyword (name : List Char) : Component → Bool
  | .token (.ident x) => sameName x name
  | _ => false

/-- The component value is an at-keyword of this name, ASCII case-insensitively. -/
def isAtKeyword (name : List Char) : Component → Bool
  | .token (.atKeyword x) => sameName x name
  | _ => false

/-- The language of an atom. `unfold` is the language of a definition that a name stands
for. -/
def Atom.language (env : Env) (unfold : Definition → Language) : Atom → Language
  | .keyword n => Language.just (isKeyword n.toList)
  | .atKeyword n => Language.just (isAtKeyword n.toList)
  | .literal c => Language.just (isDelim c)
  | .quoted t => Language.seq (t.toList.map fun c => Language.just (isDelim c))
  | .type n r =>
    match env.type n with
    | some (.basic test) => Language.just (test r)
    | some (.production d) => if r.isNone then unfold d else fun _ => false
    | none => fun _ => false
  | .functionType n =>
    match env.function n with
    | some d => unfold d
    | none => fun _ => false
  | .property n =>
    match env.property n with
    | some d => unfold d.unlisted
    | none => fun _ => false

/-- The language of an enclosure, given the language of what it holds. The flag says that
what it holds is a list whose commas may be left out: a function's arguments are one
(`comb-comma`), and brackets, parentheses and braces are not.

A function is one component value: a function of that name, ASCII case-insensitively, whose
value is admitted by the arguments (`component-functions`). Parentheses and braces written
literally are one block. -/
def Enclosure.language (inner : Bool → Language) : Enclosure → Language
  | .brackets => inner false
  | .parens => Language.just fun
    | .block .paren w => inner false (strip w)
    | _ => false
  | .braces => Language.just fun
    | .block .curly w => inner false (strip w)
    | _ => false
  | .function n => Language.just fun
    | .function x w => sameName x n.toList && inner true (strip w)
    | _ => false
  | .anyFunction => Language.just fun
    | .function _ w => inner true (strip w)
    | _ => false

/-- The definition is a comma written literally. -/
def Definition.isComma : Definition → Bool
  | .atom (.literal c) => c == ','
  | _ => false

/-- The definition is no combination: a term, with or without multipliers. A tree the reader
gives has only such parts in a juxtaposition and under a multiplier. -/
def Definition.isPart : Definition → Bool
  | .combine _ _ => false
  | _ => true

/-- The parts of a juxtaposition for `Language.args`: no language for a comma. -/
def commaParts : List Definition → List Language → List (Option Language)
  | p :: ps, l :: ls => (if p.isComma then none else some l) :: commaParts ps ls
  | _, _ => []

mutual

/-- The language of a definition. `unfold` is the language of a definition that a name stands
for. `top` says that the definition is a list whose commas may be left out: the whole of a
property's grammar or of a production, the arguments of a function, and each alternative of
such a list. -/
def Definition.language (env : Env) (unfold : Definition → Language) :
    Definition → Bool → Language
  | .atom a, _ => a.language env unfold
  | .nest e x, _ => e.language fun top => x.language env unfold top
  | .combine .seq ps, top =>
    if top && ps.any Definition.isComma then
      Language.args (commaParts ps (Definition.languages env unfold ps false)) false false
    else Language.seq (Definition.languages env unfold ps false)
  | .combine .all ps, _ => Language.allOf ps.length (Definition.languages env unfold ps false)
  | .combine .any ps, _ => Language.anyOf ps.length (Definition.languages env unfold ps false)
  | .combine .one ps, top => Language.oneOf (Definition.languages env unfold ps top)
  | .mult x m, _ => Language.mult (x.language env unfold false) m

/-- The language of each definition of a list. -/
def Definition.languages (env : Env) (unfold : Definition → Language) :
    List Definition → Bool → List Language
  | [], _ => []
  | p :: ps, top => p.language env unfold top :: Definition.languages env unfold ps top

end

/-- The language of a definition that a name stands for, with names unfolded at most `depth`
times: past that a name admits nothing. -/
def unfoldAt (env : Env) : Nat → Definition → Language
  | 0 => fun _ _ => false
  | n + 1 => fun d => d.language env (unfoldAt env n) true

/-- The definition admits the value. White space is dropped first. A name is unfolded at most
`depth` times on any path, so this ends for every environment and every value. -/
def admits (env : Env) (d : Definition) (value : List Component) (depth : Nat := 32) : Bool :=
  d.language env (unfoldAt env depth) true (strip value)

/-! ## Basic types

Each is a reading of prose of CSS Values 4, under the anchor named. A numeric type checks the
bracketed range of its use against the numeric value of the token. -/

namespace Basic

/-- A bound is at most a value. A zero bound is compared by sign alone, since every unit is a
positive size; any other bound needs the size of both units. -/
def atMost (scale : List Char → Option Rat) (b : Bound) (value : Rat) (unit : List Char) : Bool :=
  match b with
  | .negInfinity => true
  | .infinity => false
  | .finite n u =>
    if n == 0 then decide (0 ≤ value)
    else
      match scale (u.toList.map Char.toLower), scale (unit.map Char.toLower) with
      | some f, some g => decide ((n : Rat) * f ≤ value * g)
      | _, _ => false

/-- A bound is at least a value. -/
def atLeast (scale : List Char → Option Rat) (b : Bound) (value : Rat) (unit : List Char) : Bool :=
  match b with
  | .negInfinity => false
  | .infinity => true
  | .finite n u =>
    if n == 0 then decide (value ≤ 0)
    else
      match scale (u.toList.map Char.toLower), scale (unit.map Char.toLower) with
      | some f, some g => decide (value * g ≤ (n : Rat) * f)
      | _, _ => false

/-- The value is in the range (`numeric-ranges`): "a closed range between (and including) min
and max". "If no range is indicated … then `[−∞,∞]` is assumed." -/
def inRange (scale : List Char → Option Rat) (r : Option Range) (value : Rat) (unit : List Char) :
    Bool :=
  match r with
  | none => true
  | some r => atMost scale r.min value unit && atLeast scale r.max value unit

/-- The size of the unit of a plain number: it has none. -/
def unitless (u : List Char) : Option Rat := if u.isEmpty then some 1 else none

/-- `<number>` (`number-value`): "It corresponds to the `<number-token>` production". -/
def number (r : Option Range) : Component → Bool
  | .token (.number n _) => inRange unitless r n.value []
  | _ => false

/-- `<integer>` (`integer-value`): "one or more decimal digits `0` through `9`", which is a
number token whose type flag is integer. -/
def integer (r : Option Range) : Component → Bool
  | .token (.number n .integer) => inRange unitless r n.value []
  | _ => false

/-- `<percentage>` (`percentage-value`): "It corresponds to the `<percentage-token>`
production". A range is written with plain numbers: `<percentage [0,100]>`. -/
def percentage (r : Option Range) : Component → Bool
  | .token (.percentage n) => inRange unitless r n.value []
  | _ => false

/-- `<zero>` (`zero-value`): "a literal number with the value 0". -/
def zero (_ : Option Range) : Component → Bool
  | .token (.number n _) => n.value == 0
  | _ => false

/-- The size of a unit in a table: `some none` for a unit with no fixed size. -/
def lookup (units : List (String × Option Rat)) (u : List Char) : Option (Option Rat) :=
  (units.find? fun e => e.1.toList == u.map Char.toLower).map fun e => e.2

/-- A dimension of one of the units of a table (`dimensions`): "a number immediately followed
by a unit identifier", and "unit identifiers are ASCII case-insensitive". Each unit has its
size in the canonical unit, or none where its size is not fixed: such a value is compared with
a zero bound alone. `zeroToo` takes the number `0` with no unit, as `<length>` does
(`lengths`: "For zero lengths the unit identifier is optional"). -/
def dimension (units : List (String × Option Rat)) (zeroToo : Bool) (r : Option Range) :
    Component → Bool
  | .token (.dimension n _ u) =>
    (lookup units u).isSome && inRange (fun x => (lookup units x).bind id) r n.value u
  | .token (.number n _) =>
    zeroToo && n.value == 0 && inRange (fun x => (lookup units x).bind id) r 0 []
  | _ => false

/-- `<string>` (`string-value`): it "correspond[s] to the `<string-token>` production". -/
def string (_ : Option Range) : Component → Bool
  | .token (.string _) => true
  | _ => false

/-- `<ident>`: an identifier token. -/
def ident (_ : Option Range) : Component → Bool
  | .token (.ident _) => true
  | _ => false

/-- `<custom-ident>` (`custom-idents`): "any valid CSS identifier that would not be
misinterpreted as a pre-defined keyword in that property's value definition". The excluded
names are given: "Excluded keywords are excluded in all ASCII case permutations." -/
def customIdent (excluded : List String) (_ : Option Range) : Component → Bool
  | .token (.ident x) => !excluded.any fun e => sameName x e.toList
  | _ => false

/-- `<dashed-ident>` (`dashed-idents`): "it must start with two dashes". -/
def dashedIdent (_ : Option Range) : Component → Bool
  | .token (.ident ('-' :: '-' :: _)) => true
  | _ => false

end Basic

end Whatwg.Css.Values
