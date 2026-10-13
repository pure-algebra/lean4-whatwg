import Whatwg.Html.Content.Structure
import Whatwg.Css.Syntax.Build

/-!
# Whatwg.Html.Content.Structure.Selector

Owner: the selector of a place (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; the CSS half of entry
W14 of `docs/research/2026-10-12-whatwg-requests.md`).

`Whatwg/Html/Content/Structure.lean` says what a structural fact is: a place in a tree
(`Where`), and the test that an element stands there. A stylesheet draws a fact by a selector.
This module writes the selector of a place as a prelude of the one tree of CSS
(`Whatwg/Css/Syntax/Tree.lean`), from the builders of `Whatwg/Css/Syntax/Build.lean`, so that a
rule's selector is computed from the fact it draws and is never typed beside it.

- `Test.write position t`: the simple selectors of a test of one element. A type selector and
  `*` may stand only at the start of a compound selector, so the writer is told where it writes
  (`Position`). `Test.compound t` is the test as one compound selector.
- `Test.alternatives t`: what an `or` at the top of a test joins.
- `Aspect`: what a selector says of an element that no tree holds: a state (a pseudo-class by
  its name: `hover`, `focus`, `target`), asked of the element or of a place above it, and a part
  of the element's box that is no element (a pseudo-element by its name: `before`). The facts
  leave both out on purpose; a rule adds them to the selector of its fact.
- `Where.complex`: a place as one complex selector, with no comma at its top.
- `Where.selector w aspect`: **the selector of a place**, a selector list with one complex
  selector for each alternative of the place's own test. `selectorOf fact aspect` is the same
  for a fact of a vocabulary.

How each constructor is spelled. Selectors is not sealed in this repository, so every line of
this table is from memory of Selectors Level 4 and is not checked against a text.

| Term | Selector |
| --- | --- |
| `Test.any` | `*`, and nothing after another simple selector |
| `Test.named n` | `n`, and `:is(n)` after another simple selector |
| `Test.classed c` | `.c` |
| `Test.has a` | `[a]` |
| `Test.valued a v` | `[a=v]` where the value is an identifier that needs no escape (`isPlainValue`), and `[a="v"]` for any other text |
| `Test.first` | `:first-child` |
| `Test.nthLast n` | `:nth-last-child(n)` |
| `Test.not t` | `:not(…)` of the selector list of `t` |
| `Test.and a b` | the two in a row: one compound selector |
| `Test.or a b` | `:is(…)` of the two as a selector list; at the top of a place's own test, a comma |
| `Where.here t` | the compound of `t` |
| `Where.under p t` | `p > t`: the child combinator |
| `Where.inside p t` | `p t`: the descendant combinator |
| a state `s` | `:s` after the compound it is asked of |
| a part `p` | `::p` after the compound of the element |

Why an `or` at the top is a comma. `:is()` takes the specificity of its most specific argument
(from memory), so `:is(.label, dt)` weighs more on a `dt` than `dt` does. A comma gives each
alternative its own weight, as the consumer's sheet writes `.label, dt, summary`. Inside a
compound or above a combinator an alternative cannot be a comma, and is `:is()`.

The laws are in `Whatwg/Html/Content/Structure/Selector/Laws.lean`: the selector of every place
has no comment in its text, and is writable where its names are names (`Where.plain`).

What this module does not claim.

- **That a browser's selector matches exactly `places`.** That is the theorem this module
  would want, and it has no statement here: there is no model of Selectors to state it
  against. A host check should try at least these cases, where the two are known or expected to
  part:
  - a name or a value in another case. `Test.named` and `Test.valued` compare exactly. A type
    selector is compared to an HTML element in lower case, and the values of 46 attributes
    (`rel`, `type`, `scope`, `lang` among them) are compared with no regard to case (HTML
    Standard, section "Case-sensitivity of selectors", sealed under
    `vendor/whatwg-html-746f2ede/`);
  - an element in the contents of a `template`: `places` reads it as a child, and a browser
    keeps it in a fragment that no selector reaches (from memory);
  - a class in a document in quirks mode, compared there with no regard to case (from memory);
  - `Test.first` and `Test.nthLast` at the root of a tree: `places` counts no element beside
    the root, and `:first-child` holds of a root in Selectors Level 4 and not in Level 3 (from
    memory);
  - `Test.nthLast 0`, which holds of no element here and should match none;
  - an element of another namespace: `named "a"` holds of an SVG `a`, and so should the type
    selector `a` in a sheet with no default namespace.
- That a state or a part exists: `Aspect` takes any name.
- A sibling combinator. `Where` has none, so `li + li` of the consumer's sheet is written
  `li:not(:first-child)`, which selects the same items of a list whose children are all `li`.
- The weight of a selector in the cascade.

Every definition here that takes a `String` reaches `Classical.choice` through `String.toList`
of core, as the builders do. `Whatwg.Html` is under the ordinary axiom ceiling.
-/

namespace Whatwg.Html.Content.Structure

open Whatwg.Css.Syntax (Component Value Prelude)

/-! ## The test of one element -/

/-- Where a test is written in a selector. -/
inductive Position where
  /-- At the start of a compound selector: a type selector and `*` may stand here. -/
  | opens
  /-- After a simple selector of the same compound. -/
  | follows
  /-- As a selector list: an `or` at the top is a comma. -/
  | listed
  deriving DecidableEq, Repr, Inhabited

/-- Where the first part of a conjunction is written: at the start of the compound, unless the
conjunction itself follows a simple selector. -/
def Position.first : Position → Position
  | .follows => .follows
  | _ => .opens

/-- Whether the value of an attribute is written as an identifier: it is one that needs no
escape. Any other value, the empty one too, is written as a string. -/
def isPlainValue (value : String) : Bool :=
  Whatwg.Css.Syntax.isPlainIdentifier value.toList && Whatwg.Css.Syntax.isNameValue value.toList

/-- **The simple selectors of a test**, written at a position. At the start of a compound it is
never empty; after a simple selector `Test.any` writes nothing, since it holds of every
element. -/
def Test.write (position : Position) : Test → Prelude
  | .any =>
    match position with
    | .follows => []
    | _ => [.delim '*']
  | .named name =>
    match position with
    | .follows => [.colon, .call "is" [.ident name]]
    | _ => [.ident name]
  | .classed token => Prelude.class token
  | .has attr => [.brackets [.ident attr]]
  | .valued attr value =>
    if isPlainValue value then [.brackets [.ident attr, .delim '=', .ident value]]
    else Prelude.attr attr value
  | .first => [.colon, .ident "first-child"]
  | .nthLast n => [.colon, .call "nth-last-child" [.int n]]
  | .not t => [.colon, .call "not" (t.write .listed)]
  | .and a b => a.write position.first ++ b.write .follows
  | .or a b =>
    match position with
    | .listed => a.write .listed ++ .comma :: .space :: b.write .listed
    | _ => [.colon, .call "is" (a.write .listed ++ .comma :: .space :: b.write .listed)]

/-- A test as one compound selector. -/
def Test.compound (t : Test) : Prelude := t.write .opens

/-- The alternatives of a test: what an `or` at its top joins, in order. A test with no `or` at
its top is its own one alternative. -/
def Test.alternatives : Test → List Test
  | .or a b => a.alternatives ++ b.alternatives
  | t => [t]

/-! ## What no tree holds -/

/-- What a selector says of an element that no tree holds: a state, and a part of its box that
is no element. A fact is a place in a tree, and has neither. -/
structure Aspect where
  /-- A state, by the name of its pseudo-class: `hover`, `focus`, `target`. -/
  state : Option String := none
  /-- How many places above the element the state is asked of: 0 is the element, 1 the place it
  stands under or inside. A count past the top is the top. -/
  above : Nat := 0
  /-- A part of the element's box that is no element, by the name of its pseudo-element:
  `before`. -/
  part : Option String := none
  deriving DecidableEq, Repr, Inhabited

namespace Aspect

/-- The state as a pseudo-class, and nothing where there is none. -/
def stateText (aspect : Aspect) : Prelude :=
  match aspect.state with
  | some name => [.colon, .ident name]
  | none => []

/-- The part as a pseudo-element, and nothing where there is none. -/
def partText (aspect : Aspect) : Prelude :=
  match aspect.part with
  | some name => [.colon, .colon, .ident name]
  | none => []

/-- What the aspect writes after the compound `depth` places above the element; `top` says that
no place stands above that compound. The state is written at its depth, and at the top where
its depth is past the top; the part is written at the element. -/
def after (aspect : Aspect) (depth : Nat) (top : Bool) : Prelude :=
  (if depth == aspect.above || (top && decide (depth < aspect.above)) then aspect.stateText
    else []) ++
  (if depth == 0 then aspect.partText else [])

end Aspect

/-! ## A place -/

/-- Whether no place stands above the element of a place. -/
def Where.isTop : Where → Bool
  | .here _ => true
  | _ => false

/-- **A place as one complex selector**, with no comma at its top: its own compound `depth`
places above the element that a rule draws, after the places above it. -/
def Where.complex (aspect : Aspect) : Where → Nat → Prelude
  | .here t, depth => t.write .opens ++ aspect.after depth true
  | .under parent t, depth =>
    parent.complex aspect (depth + 1) ++
      .space :: .delim '>' :: .space :: (t.write .opens ++ aspect.after depth false)
  | .inside above t, depth =>
    above.complex aspect (depth + 1) ++ .space :: (t.write .opens ++ aspect.after depth false)

/-- A compound of the element of a place, after the place it stands under or inside and the
combinator between the two. -/
def Where.led (aspect : Aspect) (w : Where) (own : Prelude) : Prelude :=
  match w with
  | .here _ => own
  | .under parent _ => parent.complex aspect 1 ++ .space :: .delim '>' :: .space :: own
  | .inside above _ => above.complex aspect 1 ++ .space :: own

/-- **The selector of a place**: a selector list with one complex selector for each alternative
of the place's own test, each with the aspect. -/
def Where.selector (w : Where) (aspect : Aspect := {}) : Prelude :=
  Value.list (w.test.alternatives.map fun alternative =>
    w.led aspect (alternative.write .opens ++ aspect.after 0 w.isTop))

/-- **The selector of a fact of a vocabulary.** -/
def selectorOf {φ : Type} [Vocabulary φ] (fact : φ) (aspect : Aspect := {}) : Prelude :=
  (Vocabulary.place fact).selector aspect

/-- The selector of several places as one selector list. -/
def selectorAll (places : List Where) (aspect : Aspect := {}) : Prelude :=
  Value.list (places.map fun w => w.selector aspect)

/-! ## Names that the writer writes -/

/-- Whether the names of a test are names that the tokenizer can give: each has a code point at
least and no U+0000, and a value has no U+0000. The writer escapes what needs it, so a class
that starts with a digit is plain. -/
def Test.plain : Test → Bool
  | .any => true
  | .named name => Whatwg.Css.Syntax.isNameValue name.toList
  | .classed token => Whatwg.Css.Syntax.isNameValue token.toList
  | .has attr => Whatwg.Css.Syntax.isNameValue attr.toList
  | .valued attr value =>
    Whatwg.Css.Syntax.isNameValue attr.toList && value.toList.all fun c => c.toNat != 0
  | .first => true
  | .nthLast _ => true
  | .not t => t.plain
  | .and a b => a.plain && b.plain
  | .or a b => a.plain && b.plain

/-- Whether the names of a place are plain. -/
def Where.plain : Where → Bool
  | .here t => t.plain
  | .under parent t => parent.plain && t.plain
  | .inside above t => above.plain && t.plain

/-- Whether the names of an aspect are plain. -/
def Aspect.plain (aspect : Aspect) : Bool :=
  aspect.state.all (fun name => Whatwg.Css.Syntax.isNameValue name.toList) &&
    aspect.part.all (fun name => Whatwg.Css.Syntax.isNameValue name.toList)

end Whatwg.Html.Content.Structure
