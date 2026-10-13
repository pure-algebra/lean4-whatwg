import Whatwg.Html.Content.Structure.Selector
import Whatwg.Css.Syntax.Build.Laws

/-!
# Whatwg.Html.Content.Structure.Selector.Laws

Owner: what the selector of a place satisfies (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entry
W14 of `docs/research/2026-10-12-whatwg-requests.md`).

`Whatwg/Html/Content/Structure/Selector.lean` writes the selector of a place. This module says
that the writer of CSS can write it and that the tokenizer reads it back.

- `Where.quiet_selector`: **the selector of every place has no comment in its text**, whatever
  its names and its aspect. So the text of a selector is the texts of its tokens
  (`serialize_of_quiet` of `Whatwg/Css/Syntax/Build/Laws.lean`).
- `Where.writable_selector`: **the selector of a place is writable where its names are plain**
  (`Where.plain`, `Aspect.plain`). `Writable` is the premise under which the tokenizer reads the
  text back to the tokens (`tokenize_serialize` of `Whatwg/Css/Syntax/Laws.lean`).
- `quiet_selectorAll`, `writable_selectorAll`: the same of several places as one selector list.
- `Where.selector_of_single`: a place whose own test has no `or` at its top is one complex
  selector. `Test.write_listed`: a test as a selector list is its alternatives with a comma
  between two, so `:is()` and `:not()` take the list that a place has at its top.

How the first law is proved. A comment goes between two tokens that would read as one. Every
simple selector that follows another in a compound opens with a full stop, a left square
bracket or a colon, and no comment goes before any of the three, whatever stands before
(`quiet_append_calm`). A combinator has white space on both sides, and no comment goes beside
white space.

What this module does not claim. That the parser reads a rule of the selector back: that asks
more of a prelude than `Writable` (`Rule.readable` of `Whatwg/Css/Syntax/Readable.lean`), and
one case is known to fail it, a type selector whose name starts with two hyphen-minus before a
pseudo-class, which the parser takes for a custom property. A sheet computes the whole premise
for itself (`Sheet.writable`). And nothing of what a selector selects.

The two laws of quiet depend on `propext` and `Quot.sound` and, through the builders that take a
`String`, on `Classical.choice`; no law here reaches any other axiom.
-/

namespace Whatwg.Css.Syntax

/-! ## Lists of tokens that may follow anything -/

/-- **Two lists, the second opening with a token that no comment goes before,** are quiet
exactly when both are. -/
theorem quiet_append_calm {s : Token} (hs : ∀ a, needsComment a s = false)
    (xs ys : List Token) : Quiet (xs ++ s :: ys) = (Quiet xs && Quiet (s :: ys)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil =>
      show (!needsComment a s && Quiet (s :: ys)) = (true && Quiet (s :: ys))
      rw [hs a]
      rfl
    | cons b rest' =>
      show (!needsComment a b && Quiet ((b :: rest') ++ s :: ys)) =
        ((!needsComment a b && Quiet (b :: rest')) && Quiet (s :: ys))
      rw [ih, Bool.and_assoc]

/-- No comment goes before a colon. -/
theorem calm_colon (a : Token) : needsComment a .colon = false :=
  needsComment_right (b := .colon) rfl nofun nofun a

/-- No comment goes before a left square bracket. -/
theorem calm_openSquare (a : Token) : needsComment a .openSquare = false :=
  needsComment_right (b := .openSquare) rfl nofun nofun a

/-- No comment goes before a full stop. -/
theorem calm_fullStop (a : Token) : needsComment a (.delim '.') = false :=
  needsComment_right (b := .delim '.') rfl (by decide) (by decide) a

/-- A value that may stand after another with nothing between the two: it has no token, or no
comment goes before its first. -/
def Follows (v : Value) : Prop :=
  Component.tokensAll v = [] ∨
    ∃ s rest, Component.tokensAll v = s :: rest ∧ ∀ a, needsComment a s = false

theorem follows_nil : Follows [] := Or.inl rfl

/-- A value that opens with a token no comment goes before. -/
theorem follows_cons_token {t : Token} (ht : ∀ a, needsComment a t = false) (v : Value) :
    Follows (Component.token t :: v) :=
  Or.inr ⟨t, Component.tokensAll v, by rw [Component.tokensAll_cons]; rfl, ht⟩

/-- A value that opens with a block in square brackets. -/
theorem follows_cons_brackets (inner v : Value) : Follows (Component.brackets inner :: v) :=
  Or.inr ⟨.openSquare, (Component.tokensAll inner ++ [.closeSquare]) ++ Component.tokensAll v, by
    rw [Component.tokensAll_cons]
    show Component.tokens (.block .square inner) ++ Component.tokensAll v = _
    rw [Component.tokens]
    rfl, calm_openSquare⟩

/-- Two such values in a row are one. -/
theorem follows_append {v w : Value} (hv : Follows v) (hw : Follows w) : Follows (v ++ w) := by
  rcases hv with hv | ⟨s, rest, hv, hs⟩
  · rcases hw with hw | ⟨s, rest, hw, hs⟩
    · exact Or.inl (by rw [Component.tokensAll_append, hv, hw]; rfl)
    · exact Or.inr ⟨s, rest, by rw [Component.tokensAll_append, hv, hw]; rfl, hs⟩
  · exact Or.inr ⟨s, rest ++ Component.tokensAll w, by rw [Component.tokensAll_append, hv]; rfl, hs⟩

namespace Value

/-- **A value and one that may follow it** are quiet exactly when both are. -/
theorem quiet_append_of_follows (v : Value) {w : Value} (hw : Follows w) :
    quiet (v ++ w) = (v.quiet && w.quiet) := by
  show Quiet (Component.tokensAll (v ++ w)) =
    (Quiet (Component.tokensAll v) && Quiet (Component.tokensAll w))
  rw [Component.tokensAll_append]
  rcases hw with hw | ⟨s, rest, hw, hs⟩
  · rw [hw, List.append_nil]
    exact (Bool.and_true _).symm
  · rw [hw]
    exact quiet_append_calm hs _ _

/-- A colon before a value: quiet exactly when the value is. -/
theorem quiet_colon_cons (v : Value) : quiet (Component.colon :: v) = v.quiet :=
  quiet_cons (a := .colon) (fun _ => rfl) _

/-- Two values with a whitespace token between them are quiet exactly when both are. -/
theorem quiet_append_space (v w : Value) :
    quiet (v ++ Component.space :: w) = (v.quiet && w.quiet) := by
  show Quiet (Component.tokensAll (v ++ Component.space :: w)) = _
  rw [Component.tokensAll_append, Component.tokensAll_cons]
  exact quiet_append_whitespace _ _

/-- Two values with a comma and a whitespace token between them are quiet exactly when both
are. -/
theorem quiet_append_comma (v w : Value) :
    quiet (v ++ Component.comma :: Component.space :: w) = (v.quiet && w.quiet) := by
  show Quiet (Component.tokensAll (v ++ Component.comma :: Component.space :: w)) = _
  rw [Component.tokensAll_append, Component.tokensAll_cons, Component.tokensAll_cons]
  exact Whatwg.Css.Syntax.quiet_append_comma _ _

/-- A pseudo-class that is a function: quiet exactly when its arguments are. -/
theorem quiet_pseudo_call (name : String) (arguments : Value) :
    quiet [Component.colon, Component.call name arguments] = arguments.quiet := by
  rw [quiet_colon_cons, quiet_singleton, Component.quiet_call]

/-- A pseudo-class that is a function is writable where its name is a name that is not `url`
and its arguments are writable. -/
theorem writable_pseudo_call {name : String} {arguments : Value}
    (hn : isNameValue name.toList = true) (hu : isUrlName name.toList = false)
    (ha : arguments.writable = true) :
    writable [Component.colon, Component.call name arguments] = true :=
  writable_cons Component.writable_colon
    ((writable_singleton _).trans (Component.writable_call hn hu ha))

/-- Two writable values with a comma and a whitespace token between them are writable. -/
theorem writable_append_comma {v w : Value} (hv : v.writable = true) (hw : w.writable = true) :
    writable (v ++ Component.comma :: Component.space :: w) = true :=
  writable_append hv (writable_cons Component.writable_comma (writable_cons Component.writable_space hw))

end Value

end Whatwg.Css.Syntax

namespace Whatwg.Html.Content.Structure

open Whatwg.Css.Syntax

/-! ## The test of one element -/

/-- After a simple selector, the simple selectors of a test may follow with nothing between. -/
theorem Test.follows_write : ∀ t : Test, Follows (t.write .follows)
  | .any => follows_nil
  | .named _ => follows_cons_token calm_colon _
  | .classed _ => follows_cons_token calm_fullStop _
  | .has _ => follows_cons_brackets _ _
  | .valued attr value => by
    show Follows (if isPlainValue value = true then _ else _)
    split
    · exact follows_cons_brackets _ _
    · exact follows_cons_brackets _ _
  | .first => follows_cons_token calm_colon _
  | .nthLast _ => follows_cons_token calm_colon _
  | .not _ => follows_cons_token calm_colon _
  | .and a b => follows_append (Test.follows_write a) (Test.follows_write b)
  | .or _ _ => follows_cons_token calm_colon _

/-- **The simple selectors of a test have no comment in their text**, at every position. -/
theorem Test.quiet_write : ∀ (t : Test) (position : Position),
    Value.quiet (t.write position) = true
  | .any, .opens => rfl
  | .any, .follows => rfl
  | .any, .listed => rfl
  | .named _, .opens => rfl
  | .named _, .listed => rfl
  | .named name, .follows => (Value.quiet_pseudo_call "is" [.ident name]).trans rfl
  | .classed token, _ => Prelude.quiet_class token
  | .has attr, _ => by
    show Value.quiet [Component.block .square [.ident attr]] = true
    rw [Value.quiet_singleton, Component.quiet_block]
    rfl
  | .valued attr value, _ => by
    show Value.quiet (if isPlainValue value = true then _ else _) = true
    split
    · rw [Value.quiet_singleton]
      show Component.quiet (.block .square [.ident attr, .delim '=', .ident value]) = true
      rw [Component.quiet_block]
      show (!needsComment (.ident attr.toList) (.delim '=') &&
        Quiet [Token.delim '=', Token.ident value.toList]) = true
      rw [needsComment_right (b := .delim '=') rfl (by decide) (by decide)]
      rfl
    · exact Prelude.quiet_attr attr value
  | .first, _ => (Value.quiet_colon_cons _).trans rfl
  | .nthLast n, _ => (Value.quiet_pseudo_call "nth-last-child" [.int n]).trans rfl
  | .not t, _ => (Value.quiet_pseudo_call "not" _).trans (Test.quiet_write t .listed)
  | .and a b, position => by
    show Value.quiet (a.write position.first ++ b.write .follows) = true
    rw [Value.quiet_append_of_follows _ (Test.follows_write b), Test.quiet_write a,
      Test.quiet_write b]
    rfl
  | .or a b, .listed => by
    show Value.quiet (a.write .listed ++ Component.comma :: Component.space :: b.write .listed) = true
    rw [Value.quiet_append_comma, Test.quiet_write a, Test.quiet_write b]
    rfl
  | .or a b, .opens => by
    refine (Value.quiet_pseudo_call "is" _).trans ?_
    rw [Value.quiet_append_comma, Test.quiet_write a, Test.quiet_write b]
    rfl
  | .or a b, .follows => by
    refine (Value.quiet_pseudo_call "is" _).trans ?_
    rw [Value.quiet_append_comma, Test.quiet_write a, Test.quiet_write b]
    rfl

/-- **The simple selectors of a test are writable where its names are plain**, at every
position. -/
theorem Test.writable_write : ∀ (t : Test) (position : Position), t.plain = true →
    Value.writable (t.write position) = true
  | .any, .opens, _ => by decide
  | .any, .follows, _ => rfl
  | .any, .listed, _ => by decide
  | .named name, .opens, h =>
    (Value.writable_singleton _).trans ((Component.writable_ident name).trans h)
  | .named name, .listed, h =>
    (Value.writable_singleton _).trans ((Component.writable_ident name).trans h)
  | .named name, .follows, h =>
    Value.writable_pseudo_call (name := "is") (by decide) (by decide)
      ((Value.writable_singleton _).trans ((Component.writable_ident name).trans h))
  | .classed _, _, h => Prelude.writable_class h
  | .has attr, _, h =>
    (Value.writable_singleton _).trans (Component.writable_block .square
      ((Value.writable_singleton _).trans ((Component.writable_ident attr).trans h)))
  | .valued attr value, _, h => by
    show Value.writable (if isPlainValue value = true then _ else _) = true
    split
    · rename_i hplain
      exact (Value.writable_singleton _).trans (Component.writable_block .square
        (Value.writable_cons ((Component.writable_ident attr).trans (Bool.and_eq_true_iff.mp h).1)
          (Value.writable_cons (c := .delim '=') rfl
            ((Value.writable_singleton _).trans
              ((Component.writable_ident value).trans (Bool.and_eq_true_iff.mp hplain).2)))))
    · exact Prelude.writable_attr (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2
  | .first, _, _ =>
    Value.writable_cons Component.writable_colon
      ((Value.writable_singleton _).trans ((Component.writable_ident "first-child").trans (by decide)))
  | .nthLast n, _, _ =>
    Value.writable_pseudo_call (name := "nth-last-child") (by decide) (by decide)
      ((Value.writable_singleton _).trans (Component.writable_int n))
  | .not t, _, h =>
    Value.writable_pseudo_call (name := "not") (by decide) (by decide) (Test.writable_write t .listed h)
  | .and a b, position, h =>
    Value.writable_append (Test.writable_write a position.first (Bool.and_eq_true_iff.mp h).1)
      (Test.writable_write b .follows (Bool.and_eq_true_iff.mp h).2)
  | .or a b, .listed, h =>
    Value.writable_append_comma (Test.writable_write a .listed (Bool.and_eq_true_iff.mp h).1)
      (Test.writable_write b .listed (Bool.and_eq_true_iff.mp h).2)
  | .or a b, .opens, h =>
    Value.writable_pseudo_call (name := "is") (by decide) (by decide)
      (Value.writable_append_comma (Test.writable_write a .listed (Bool.and_eq_true_iff.mp h).1)
        (Test.writable_write b .listed (Bool.and_eq_true_iff.mp h).2))
  | .or a b, .follows, h =>
    Value.writable_pseudo_call (name := "is") (by decide) (by decide)
      (Value.writable_append_comma (Test.writable_write a .listed (Bool.and_eq_true_iff.mp h).1)
        (Test.writable_write b .listed (Bool.and_eq_true_iff.mp h).2))

/-- The alternatives of a test whose names are plain have plain names. -/
theorem Test.plain_of_mem_alternatives : ∀ {t : Test}, t.plain = true →
    ∀ alternative ∈ t.alternatives, alternative.plain = true
  | .or a b, h, alternative, hmem => by
    rcases List.mem_append.mp hmem with ha | hb
    · exact Test.plain_of_mem_alternatives (Bool.and_eq_true_iff.mp h).1 alternative ha
    · exact Test.plain_of_mem_alternatives (Bool.and_eq_true_iff.mp h).2 alternative hb
  | .any, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .named _, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .classed _, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .has _, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .valued _ _, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .first, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .nthLast _, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .not _, h, _, hmem => List.mem_singleton.mp hmem ▸ h
  | .and _ _, h, _, hmem => List.mem_singleton.mp hmem ▸ h

/-! ## A selector list, at the top and in a function -/

/-- Two rows of values as one list of values: the two lists, with a comma between. -/
theorem list_append : ∀ (xs ys : List Value), xs ≠ [] → ys ≠ [] →
    Value.list (xs ++ ys) =
      Value.list xs ++ Component.comma :: Component.space :: Value.list ys
  | [], _, h, _ => absurd rfl h
  | [_], [], _, h => absurd rfl h
  | [x], y :: ys, _, _ => by
    rw [List.singleton_append, Value.list, Value.list]
  | x :: x' :: xs, ys, _, hy => by
    rw [List.cons_append, List.cons_append, Value.list, ← List.cons_append,
      list_append (x' :: xs) ys (List.cons_ne_nil _ _) hy, Value.list, List.append_assoc]
    rfl

/-- A test has an alternative at least. -/
theorem Test.alternatives_ne_nil : ∀ t : Test, t.alternatives ≠ []
  | .or a _ => fun h => Test.alternatives_ne_nil a (List.append_eq_nil_iff.mp h).1
  | .any => List.cons_ne_nil _ _
  | .named _ => List.cons_ne_nil _ _
  | .classed _ => List.cons_ne_nil _ _
  | .has _ => List.cons_ne_nil _ _
  | .valued _ _ => List.cons_ne_nil _ _
  | .first => List.cons_ne_nil _ _
  | .nthLast _ => List.cons_ne_nil _ _
  | .not _ => List.cons_ne_nil _ _
  | .and _ _ => List.cons_ne_nil _ _

/-- **A test as a selector list is its alternatives, each a compound, with a comma between
two.** So `:is()` and `:not()` take the list that a place has at its top. -/
theorem Test.write_listed : ∀ t : Test,
    t.write .listed = Value.list (t.alternatives.map fun alternative => alternative.write .opens)
  | .or a b => by
    have hne : ∀ t : Test, (t.alternatives.map fun alternative => alternative.write .opens) ≠ [] :=
      fun t h => Test.alternatives_ne_nil t (List.map_eq_nil_iff.mp h)
    show a.write .listed ++ Component.comma :: Component.space :: b.write .listed =
      Value.list ((a.alternatives ++ b.alternatives).map fun alternative => alternative.write .opens)
    rw [List.map_append, list_append _ _ (hne a) (hne b), ← Test.write_listed a,
      ← Test.write_listed b]
  | .any => rfl
  | .named _ => rfl
  | .classed _ => rfl
  | .has _ => rfl
  | .valued _ _ => rfl
  | .first => rfl
  | .nthLast _ => rfl
  | .not _ => rfl
  | .and _ _ => rfl

/-! ## What no tree holds -/

namespace Aspect

theorem follows_stateText (aspect : Aspect) : Follows aspect.stateText := by
  unfold stateText
  split
  · exact follows_cons_token calm_colon _
  · exact follows_nil

theorem follows_partText (aspect : Aspect) : Follows aspect.partText := by
  unfold partText
  split
  · exact follows_cons_token calm_colon _
  · exact follows_nil

theorem quiet_stateText (aspect : Aspect) : Value.quiet aspect.stateText = true := by
  unfold stateText
  split
  · exact (Value.quiet_colon_cons _).trans rfl
  · rfl

theorem quiet_partText (aspect : Aspect) : Value.quiet aspect.partText = true := by
  unfold partText
  split
  · exact (Value.quiet_colon_cons _).trans ((Value.quiet_colon_cons _).trans rfl)
  · rfl

/-- What an aspect writes may follow a compound with nothing between. -/
theorem follows_after (aspect : Aspect) (depth : Nat) (top : Bool) :
    Follows (aspect.after depth top) := by
  unfold after
  refine follows_append ?_ ?_
  · split
    · exact follows_stateText aspect
    · exact follows_nil
  · split
    · exact follows_partText aspect
    · exact follows_nil

/-- What an aspect writes has no comment in its text. -/
theorem quiet_after (aspect : Aspect) (depth : Nat) (top : Bool) :
    Value.quiet (aspect.after depth top) = true := by
  unfold after
  have hstate : Value.quiet
      (if (depth == aspect.above || (top && decide (depth < aspect.above))) = true then
        aspect.stateText else []) = true := by
    split
    · exact quiet_stateText aspect
    · rfl
  have hpart : Value.quiet (if (depth == 0) = true then aspect.partText else []) = true := by
    split
    · exact quiet_partText aspect
    · rfl
  have hfollows : Follows (if (depth == 0) = true then aspect.partText else []) := by
    split
    · exact follows_partText aspect
    · exact follows_nil
  rw [Value.quiet_append_of_follows _ hfollows, hstate, hpart]
  rfl

/-- What an aspect writes is writable where its names are plain. -/
theorem writable_after {aspect : Aspect} (h : aspect.plain = true) (depth : Nat) (top : Bool) :
    Value.writable (aspect.after depth top) = true := by
  have hboth := Bool.and_eq_true_iff.mp h
  have hstate : Value.writable aspect.stateText = true := by
    unfold stateText
    cases hs : aspect.state with
    | none => rfl
    | some name =>
      have hname : isNameValue name.toList = true := by
        have := hboth.1
        rw [hs] at this
        exact this
      exact Value.writable_cons Component.writable_colon
        ((Value.writable_singleton _).trans ((Component.writable_ident name).trans hname))
  have hpart : Value.writable aspect.partText = true := by
    unfold partText
    cases hp : aspect.part with
    | none => rfl
    | some name =>
      have hname : isNameValue name.toList = true := by
        have := hboth.2
        rw [hp] at this
        exact this
      exact Value.writable_cons Component.writable_colon
        (Value.writable_cons Component.writable_colon
          ((Value.writable_singleton _).trans ((Component.writable_ident name).trans hname)))
  unfold after
  refine Value.writable_append ?_ ?_
  · split
    · exact hstate
    · rfl
  · split
    · exact hpart
    · rfl

end Aspect

/-! ## A place -/

/-- A compound with its aspect has no comment in its text. -/
theorem quiet_compound (t : Test) (aspect : Aspect) (depth : Nat) (top : Bool) :
    Value.quiet (t.write .opens ++ aspect.after depth top) = true := by
  rw [Value.quiet_append_of_follows _ (Aspect.follows_after aspect depth top),
    Test.quiet_write, Aspect.quiet_after]
  rfl

/-- A compound with its aspect is writable where the names are plain. -/
theorem writable_compound {t : Test} {aspect : Aspect} (ht : t.plain = true)
    (ha : aspect.plain = true) (depth : Nat) (top : Bool) :
    Value.writable (t.write .opens ++ aspect.after depth top) = true :=
  Value.writable_append (Test.writable_write t .opens ht) (Aspect.writable_after ha depth top)

/-- A value after a child combinator: quiet exactly when the two are. -/
theorem quiet_child (v w : Value) :
    Value.quiet (v ++ Component.space :: Component.delim '>' :: Component.space :: w) =
      (v.quiet && w.quiet) := by
  rw [Value.quiet_append_space, Value.quiet_cons_space]
  rfl

/-- A value after a child combinator is writable where the two are. -/
theorem writable_child {v w : Value} (hv : v.writable = true) (hw : w.writable = true) :
    Value.writable (v ++ Component.space :: Component.delim '>' :: Component.space :: w) = true :=
  Value.writable_append hv (Value.writable_cons Component.writable_space
    (Value.writable_cons (c := .delim '>') (by decide)
      (Value.writable_cons Component.writable_space hw)))

/-- A value after a descendant combinator is writable where the two are. -/
theorem writable_descendant {v w : Value} (hv : v.writable = true) (hw : w.writable = true) :
    Value.writable (v ++ Component.space :: w) = true :=
  Value.writable_append hv (Value.writable_cons Component.writable_space hw)

/-- **A place as one complex selector has no comment in its text.** -/
theorem Where.quiet_complex (aspect : Aspect) : ∀ (w : Where) (depth : Nat),
    Value.quiet (w.complex aspect depth) = true
  | .here t, depth => quiet_compound t aspect depth true
  | .under parent t, depth => by
    rw [Where.complex, quiet_child, Where.quiet_complex aspect parent, quiet_compound]
    rfl
  | .inside above t, depth => by
    rw [Where.complex, Value.quiet_append_space, Where.quiet_complex aspect above, quiet_compound]
    rfl

/-- **A place as one complex selector is writable where the names are plain.** -/
theorem Where.writable_complex {aspect : Aspect} (ha : aspect.plain = true) :
    ∀ (w : Where) (depth : Nat), w.plain = true → Value.writable (w.complex aspect depth) = true
  | .here _, depth, h => writable_compound h ha depth true
  | .under parent _, depth, h =>
    writable_child (Where.writable_complex ha parent (depth + 1) (Bool.and_eq_true_iff.mp h).1)
      (writable_compound (Bool.and_eq_true_iff.mp h).2 ha depth false)
  | .inside above _, depth, h =>
    writable_descendant (Where.writable_complex ha above (depth + 1) (Bool.and_eq_true_iff.mp h).1)
      (writable_compound (Bool.and_eq_true_iff.mp h).2 ha depth false)

/-- A quiet compound after the place above it has no comment in its text. -/
theorem Where.quiet_led (aspect : Aspect) (w : Where) {own : Prelude}
    (h : Value.quiet own = true) : Value.quiet (w.led aspect own) = true := by
  cases w with
  | here t => exact h
  | under parent t =>
    show Value.quiet (parent.complex aspect 1 ++
      Component.space :: Component.delim '>' :: Component.space :: own) = true
    rw [quiet_child, Where.quiet_complex, h]
    rfl
  | inside above t =>
    show Value.quiet (above.complex aspect 1 ++ Component.space :: own) = true
    rw [Value.quiet_append_space, Where.quiet_complex, h]
    rfl

/-- The names of the test of a place with plain names are plain. -/
theorem Where.plain_test {w : Where} (h : w.plain = true) : w.test.plain = true := by
  cases w with
  | here t => exact h
  | under parent t => exact (Bool.and_eq_true_iff.mp h).2
  | inside above t => exact (Bool.and_eq_true_iff.mp h).2

/-- A writable compound after the place above it is writable, where the names are plain. -/
theorem Where.writable_led {aspect : Aspect} (ha : aspect.plain = true) {w : Where}
    (hw : w.plain = true) {own : Prelude} (h : Value.writable own = true) :
    Value.writable (w.led aspect own) = true := by
  cases w with
  | here t => exact h
  | under parent t =>
    exact writable_child (Where.writable_complex ha parent 1 (Bool.and_eq_true_iff.mp hw).1) h
  | inside above t =>
    exact writable_descendant (Where.writable_complex ha above 1 (Bool.and_eq_true_iff.mp hw).1) h

/-- **The selector of every place has no comment in its text**, whatever its names and its
aspect: its text is the texts of its tokens, one after another. -/
theorem Where.quiet_selector (w : Where) (aspect : Aspect := {}) :
    Value.quiet (w.selector aspect) = true := by
  unfold Where.selector
  rw [Value.quiet_list, List.all_eq_true]
  intro own hown
  obtain ⟨alternative, -, rfl⟩ := List.mem_map.mp hown
  exact Where.quiet_led aspect w (quiet_compound alternative aspect 0 w.isTop)

/-- **The selector of a place is writable where its names are plain**: the tokenizer reads its
text back to its tokens. -/
theorem Where.writable_selector {w : Where} {aspect : Aspect} (hw : w.plain = true)
    (ha : aspect.plain = true) : Value.writable (w.selector aspect) = true := by
  unfold Where.selector
  refine Value.writable_list fun own hown => ?_
  obtain ⟨alternative, hmem, rfl⟩ := List.mem_map.mp hown
  exact Where.writable_led ha hw
    (writable_compound (Test.plain_of_mem_alternatives (Where.plain_test hw) alternative hmem) ha 0
      w.isTop)

/-- **A place whose own test has no `or` at its top is one complex selector.** -/
theorem Where.selector_of_single {w : Where} (h : w.test.alternatives = [w.test])
    (aspect : Aspect := {}) : w.selector aspect = w.complex aspect 0 := by
  unfold Where.selector
  rw [h]
  cases w with
  | here t => rfl
  | under parent t => rfl
  | inside above t => rfl

/-- The selector of a fact of a vocabulary has no comment in its text. -/
theorem quiet_selectorOf {φ : Type} [Vocabulary φ] (fact : φ) (aspect : Aspect := {}) :
    Value.quiet (selectorOf fact aspect) = true :=
  Where.quiet_selector _ aspect

/-- **Several places as one selector list have no comment in their text.** -/
theorem quiet_selectorAll (places : List Where) (aspect : Aspect := {}) :
    Value.quiet (selectorAll places aspect) = true := by
  unfold selectorAll
  rw [Value.quiet_list, List.all_eq_true]
  intro own hown
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hown
  exact Where.quiet_selector w aspect

/-- **Several places as one selector list are writable where their names are plain.** -/
theorem writable_selectorAll {places : List Where} {aspect : Aspect}
    (hw : ∀ w ∈ places, w.plain = true) (ha : aspect.plain = true) :
    Value.writable (selectorAll places aspect) = true := by
  unfold selectorAll
  refine Value.writable_list fun own hown => ?_
  obtain ⟨w, hmem, rfl⟩ := List.mem_map.mp hown
  exact Where.writable_selector (hw w hmem) ha

end Whatwg.Html.Content.Structure
