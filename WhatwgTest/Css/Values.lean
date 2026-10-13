import Whatwg.Css.Values.Admits.Laws
import WhatwgTest.Css.Corpus

/-!
# WhatwgTest.Css.Values

Owner: the test of the Value Definition Syntax as data (slice K3 of
`docs/CSS-PACKAGE-PLAN.md`; rulings CS-4 and CS-5).

1. The reader over every collected line (`WhatwgTest/Css/Corpus.lean`): each is read, the tree
   is one with `wf`, and printing it gives the line back. "Back" is said twice: the two texts
   are equal once every white space character is removed from both, and the two texts cut
   into the same lexemes.
2. The standard's own examples, from the sealed text of CSS Values 4: the two lines it calls
   equivalent, the two grammars it calls distinct, and the eight calls of `example(…)` under
   `comb-comma`.
3. The values the picture kit writes, admitted by the definitions read from the sealed
   sources: the `animation` shorthand, `translate`, `scale`, `opacity`, `linear()`,
   `cubic-bezier()` and a `transform` list. Each value is a text of a guard of
   `WhatwgTest/Html/SvgMotion.lean`, or what the writer of `Whatwg/Html/Node/SvgMotion.lean`
   gives by its rule.
4. Controls: a value that is one keyword off, a list with a comma missing, and a `||` with a
   part twice are refused.

A component value is built by hand here. The tokenizer and the parser of slice K2 will give
them from the text, and then a value of this module is the text itself.

What this module does not claim: that the collector found every definition of a source, that
an environment built here is the one a generated data module will hold, or that a browser
takes or refuses any of these values.
-/

namespace WhatwgTest.Css

open Whatwg.Css.Values
open Whatwg.Css.Syntax (Component Token)

/-! ## The reader over every collected line -/

/-- A text with every white space character removed. -/
def squeeze (s : String) : List Char := s.toList.filter fun c => !isSpace c

/-- The line is read, its tree is one the printer writes with nothing lost, and printing it
gives the line back: the same characters but for white space, and the same lexemes. -/
def Line.reads (l : Line) : Bool :=
  match Definition.read l.text with
  | none => false
  | some d =>
    d.wf && squeeze d.print == squeeze l.text && lex d.print.toList == lex l.text.toList

-- The lines of the blocks the brief names: 28 `Value:` and `New values:` fields of `propdef`
-- blocks, 38 `Value:` fields of `descdef` blocks, 120 productions of `class=prod` elements.
#guard (corpus.filter fun l => l.kind == "propdef").length == 28
#guard (corpus.filter fun l => l.kind == "descdef").length == 38
#guard (corpus.filter fun l => l.kind == "prod").length == 120
#guard corpus.length == 186

-- Every one is read and printed back. None is refused.
#guard (corpus.filter fun l => !l.reads).length == 0

-- The productions of a `<pre>` with no class, which the brief's rule does not collect: the
-- grammar of a media query, `@keyframes` and `<keyframes-name>` are among them.
#guard corpusPre.length == 26
#guard (corpusPre.filter fun l => !l.reads).length == 0

-- The three lines of debt D97. `<points>` is `DataTypePoints` of `master/shapes.html` of SVG 2,
-- and the Value column of `viewBox` is under `ViewBoxAttribute` of `master/coords.html`: both
-- are read. The third is no line of this language: `svg-translate` of CSS Transforms 1 is
-- written in the Backus-Naur Form its section defines, with literals in double quotes.
#guard ((Definition.read "[ <number>+ ]#").map Definition.print) == some "[ <number>+ ]#"
#guard ((Definition.read "[<min-x>,? <min-y>,? <width>,? <height>]").map Definition.print) ==
  some "[ <min-x> ,? <min-y> ,? <width> ,? <height> ]"
#guard (Definition.read
  "\"translate\" wsp* \"(\" wsp* number ( comma-wsp? number )? wsp* \")\"").isNone

-- What the reader refuses, each for the reason the module's header gives.
#guard ["a??", "a!", "a*+", "a#{2}{3}", "a | | b", "[ a", "a ]", "foo()", "<number [0.5,1]>",
  "a{1, 2}", "<function-token> a"].all fun s => (Definition.read s).isNone

/-! ## The standard's own examples -/

/-- A text of this module as a tree. A text that is not read is a keyword no value has. -/
def tree (s : String) : Definition := (Definition.read s).getD (.keyword "unread")

mutual

/-- A tree with its brackets removed: what each bracket holds stands in its place. -/
def ungroup : Definition → Definition
  | .atom a => .atom a
  | .nest .brackets x => ungroup x
  | .nest e x => .nest e (ungroup x)
  | .combine c ps => .combine c (ungroupAll ps)
  | .mult x m => .mult (ungroup x) m

/-- The same, for each tree of a list. -/
def ungroupAll : List Definition → List Definition
  | [] => []
  | p :: ps => ungroup p :: ungroupAll ps

end

-- `component-combinators`: "Thus, the following lines are equivalent". The first is read as
-- the tree that the brackets of the second spell out.
#guard Definition.read "a b   |   c ||   d &&   e f" ==
  some (.one [.seq [.keyword "a", .keyword "b"],
    .any [.keyword "c", .all [.keyword "d", .seq [.keyword "e", .keyword "f"]]]])
#guard Definition.read "a b   |   c ||   d &&   e f" ==
  (Definition.read "[ a b ] | [ c || [ d && [ e f ]]]").map ungroup

/-- An identifier. -/
def word (s : String) : Component := .token (.ident s.toList)

/-- A white space token. -/
def ws : Component := .token .whitespace

/-- A comma token. -/
def comma : Component := .token .comma

/-- An environment with no name. -/
def noNames : Env := Env.ofLists [] [] []

-- `component-combinators`: "`a || b || c` and `a || [ b || c ]` are distinct grammars: the
-- first allows a value like `b a c`, but the second does not."
#guard admits noNames (tree "a || b || c") [word "b", ws, word "a", ws, word "c"]
#guard !admits noNames (tree "a || [ b || c ]") [word "b", ws, word "a", ws, word "c"]
#guard admits noNames (tree "a || [ b || c ]") [word "c", ws, word "b", ws, word "a"]

/-- A function with its arguments. -/
def call (name : String) (arguments : List Component) : Component :=
  .function name.toList arguments

/-- The standard's example under `comb-comma`. -/
def example3 : Definition := tree "example( first? , second? , third? )"

-- "writing `example(first, second, third)` is valid, as is `example(first, second)` or
-- `example(first, third)` or `example(second)`."
#guard admits noNames example3
  [call "example" [word "first", comma, ws, word "second", comma, ws, word "third"]]
#guard admits noNames example3 [call "example" [word "first", comma, ws, word "second"]]
#guard admits noNames example3 [call "example" [word "first", comma, ws, word "third"]]
#guard admits noNames example3 [call "example" [word "second"]]

-- "However, `example(first, , third)` is invalid …; similarly, `example(,second)` and
-- `example(first,)` are invalid. `example(first second)` is also invalid".
#guard !admits noNames example3
  [call "example" [word "first", comma, ws, comma, ws, word "third"]]
#guard !admits noNames example3 [call "example" [comma, word "second"]]
#guard !admits noNames example3 [call "example" [word "first", comma]]
#guard !admits noNames example3 [call "example" [word "first", ws, word "second"]]

-- Where a comma may be left out. `comb-comma` names "a top-level list in a property or other
-- CSS value, or a function's argument list", so a comma inside brackets is always asked for.
-- Both ways of writing "an optional `a`, then a comma, then `b`" then say the same.
#guard ["[ a , ]? b", "a? , b"].all fun s =>
  admits noNames (tree s) [word "a", comma, ws, word "b"] &&
    admits noNames (tree s) [word "b"] &&
    !admits noNames (tree s) [word "a", ws, word "b"] &&
    !admits noNames (tree s) [comma, ws, word "b"]

-- The table `combinator-multiplier-patterns`: zero or more, one or more, and all, in order
-- and in any order.
#guard admits noNames (tree "A? B? C?") [] &&
  admits noNames (tree "A? B? C?") [word "a", ws, word "c"]
#guard !admits noNames (tree "A? B? C?") [word "c", ws, word "a"]
#guard admits noNames (tree "A? || B? || C?") [] &&
  admits noNames (tree "A? || B? || C?") [word "c", ws, word "a"]
#guard !admits noNames (tree "[ A? B? C? ]!") [] &&
  admits noNames (tree "[ A? B? C? ]!") [word "b"]
#guard !admits noNames (tree "A || B || C") [] &&
  admits noNames (tree "A || B || C") [word "c", ws, word "a"]
#guard admits noNames (tree "A && B && C") [word "c", ws, word "a", ws, word "b"]
#guard !admits noNames (tree "A && B && C") [word "c", ws, word "a"]

/-! ## The definitions read from the sealed sources -/

/-- The collected lines of some modules, each with its tree, the lines of the first module
first: where two modules define one name, the first is the one. -/
def linesOf (modules : List String) : List (Line × Definition) :=
  modules.flatMap fun m => (corpus ++ corpusPre).filterMap fun l =>
    if l.module == m then (Definition.read l.text).map fun d => (l, d) else none

/-- What stands between `<` and `>` of a name. -/
def angled (n : String) : Option (List Char) :=
  match n.toList with
  | '<' :: t => if t.getLast? == some '>' then some t.dropLast else none
  | _ => none

/-- A name that ends in `()`, without them. -/
def called (cs : List Char) : Option (List Char) :=
  match cs.reverse with
  | ')' :: '(' :: r => some r.reverse
  | _ => none

/-- The productions that define `<name>`. -/
def typeEntries (ls : List (Line × Definition)) : List (String × Meaning) :=
  ls.filterMap fun (l, d) =>
    if l.kind == "prod" || l.kind == "pre" then
      match angled l.name with
      | some cs => if (called cs).isSome then none else some (String.ofList cs, .production d)
      | none => none
    else none

/-- The productions that define `name()`, written so or as `<name()>`. -/
def functionEntries (ls : List (Line × Definition)) : List (String × Definition) :=
  ls.filterMap fun (l, d) =>
    if l.kind == "prod" then
      (called ((angled l.name).getD l.name.toList)).map fun cs => (String.ofList cs, d)
    else none

/-- The `Value:` field of each property. -/
def propertyEntries (ls : List (Line × Definition)) : List (String × Definition) :=
  ls.filterMap fun (l, d) => if l.kind == "propdef" then some (l.name, d) else none

/-- The units of `<length>` with a fixed size, in pixels: the table under `absolute-lengths`
of CSS Values 4 ("1cm = 96px/2.54", "1mm = 1/10th of 1cm", "1Q = 1/40th of 1cm", "1in = 2.54cm
= 96px", "1pc = 1/6th of 1in", "1pt = 1/72nd of 1in"). The relative units are left out of this
test. -/
def lengthUnits : List (String × Option Rat) :=
  [("px", some 1), ("cm", some ((9600 : Rat) / 254)), ("mm", some ((960 : Rat) / 254)),
    ("q", some ((240 : Rat) / 254)), ("in", some 96), ("pc", some 16), ("pt", some ((4 : Rat) / 3))]

/-- The units of `<time>`, in seconds (`time`): "There are 1000 milliseconds in a second." -/
def timeUnits : List (String × Option Rat) := [("s", some 1), ("ms", some ((1 : Rat) / 1000))]

/-- The units of `<angle>`, in degrees (`angles`): 360 degrees, 400 gradians and one turn in a
full circle. A radian has no exact size here. -/
def angleUnits : List (String × Option Rat) :=
  [("deg", some 1), ("grad", some ((9 : Rat) / 10)), ("turn", some 360), ("rad", none)]

/-- The basic types of this test. The names a `<custom-ident>` may not be are the CSS-wide
keywords of the heading `common-keywords` and `default` (`custom-idents`). -/
def basics : List (String × Meaning) :=
  [("number", .basic Basic.number), ("integer", .basic Basic.integer),
    ("percentage", .basic Basic.percentage), ("zero", .basic Basic.zero),
    ("length", .basic (Basic.dimension lengthUnits true)),
    ("time", .basic (Basic.dimension timeUnits false)),
    ("angle", .basic (Basic.dimension angleUnits false)),
    ("string", .basic Basic.string), ("ident", .basic Basic.ident),
    ("custom-ident", .basic (Basic.customIdent ["initial", "inherit", "unset", "default"])),
    ("dashed-ident", .basic Basic.dashedIdent)]

/-- Two names that the sources define outside a production line.

- `<length-percentage>` is "Equivalent to `[ <length> | <percentage> ]`" (`mixed-percentages`
  of CSS Values 4): the line the collector found at line 1572, which carries no name.
- `<transform-function>` is defined in prose (`transform-functions` of CSS Transforms 1): "The
  set of allowed transform functions is given below." It is one of the eleven functions that
  section defines, each as it is read. -/
def named (ls : List (Line × Definition)) : List (String × Meaning) :=
  (ls.filterMap fun (l, d) =>
    if l.module == "css-values-4" && l.line == 1572 then
      some ("length-percentage", Meaning.production d)
    else none) ++
  [("transform-function", .production (.one (ls.filterMap fun (l, d) =>
    if l.module == "css-transforms-1" && l.kind == "prod" && (called l.name.toList).isSome then
      some d
    else none)))]

/-- The environment of some modules, the first module first. -/
def envOf (modules : List String) : Env :=
  let ls := linesOf modules
  Env.ofLists (basics ++ named ls ++ typeEntries ls) (functionEntries ls) (propertyEntries ls)

/-- The environment of the picture kit's properties: `animation` of CSS Animations 1, easing
of CSS Easing 2, `translate` and `scale` of CSS Transforms 2, `transform` of CSS Transforms 1,
`opacity` of CSS Color 4. -/
def env : Env :=
  envOf ["css-animations-1", "css-easing-2", "css-transforms-1", "css-transforms-2", "css-color-4",
    "css-values-4"]

/-- The same with `animation` of CSS Animations 2, whose `<single-animation>` names the
grammars of two properties. -/
def env2 : Env :=
  envOf ["css-animations-2", "css-animations-1", "css-easing-2", "css-values-4"]

/-- The value is one of the property, in an environment. -/
def allows (e : Env) (property : String) (value : List Component) : Bool :=
  match e.property property with
  | some d => admits e d value
  | none => false

-- The environment holds what the tests below name: no value is refused for a missing name.
#guard ["animation", "animation-timing-function", "animation-duration", "animation-delay",
  "animation-fill-mode", "translate", "scale", "opacity", "transform", "transform-box",
  "transform-origin"].all fun p => (env.property p).isSome
#guard ["single-animation", "easing-function", "keyframes-name", "transform-list",
  "transform-function", "length-percentage", "opacity-value"].all fun n => (env.type n).isSome
#guard ["linear", "cubic-bezier", "steps"].all fun n => (env.function n).isSome
#guard ((linesOf ["css-transforms-1"]).filter fun (l, _) =>
  l.kind == "prod" && (called l.name.toList).isSome).length == 11

/-! ## The values the picture kit writes -/

/-- A number with a fraction: the mantissa over a power of ten. -/
def num (mantissa : Int) (places : Nat) : Component :=
  .token (.number ⟨(mantissa : Rat) / (10 ^ places : Nat), none⟩ .number)

/-- A whole number. -/
def int (n : Int) : Component := .token (.number ⟨n, none⟩ .integer)

/-- A dimension: the mantissa over a power of ten, and the unit. -/
def dim (mantissa : Int) (places : Nat) (unit : String) : Component :=
  .token (.dimension ⟨(mantissa : Rat) / (10 ^ places : Nat), none⟩
    (if places == 0 then .integer else .number) unit.toList)

/-- A percentage. -/
def pct (n : Int) : Component := .token (.percentage ⟨n, none⟩)

/-- Components with a comma and a space between two of them, as the kit writes arguments. -/
def commas : List Component → List Component
  | [] => []
  | [c] => [c]
  | c :: cs => c :: comma :: ws :: commas cs

/-- Components with a space between two of them. -/
def spaced : List Component → List Component
  | [] => []
  | [c] => [c]
  | c :: cs => c :: ws :: spaced cs

/-- `cubic-bezier(0.333333, y1, 0.666667, y2)`, with the heights in thousandths. -/
def bezier (y1 y2 : Int) : Component :=
  call "cubic-bezier" (commas [num 333333 6, num y1 3, num 666667 6, num y2 3])

/-- The spring of the kit as `linear()`: its twenty-one stops, in thousandths. -/
def spring : Component :=
  call "linear" (commas ([0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045,
    1041, 1034, 1026, 1019, 1012, 1007, 1003, 1000].map fun (v : Int) => num v 3))

-- The `animation` shorthand, as `WhatwgTest/Html/SvgMotion.lean` held it at `c33ce29`:
-- `m2 94.2ms cubic-bezier(0.333333, 1, 0.666667, 1) 180ms both`.
#guard allows env "animation"
  (spaced [word "m2", dim 942 1 "ms", bezier 1000 1000, dim 180 0 "ms", word "both"])

-- `m4 150ms cubic-bezier(0.333333, 0, 0.666667, 0) 0ms both`.
#guard allows env "animation"
  (spaced [word "m4", dim 150 0 "ms", bezier 0 0, dim 0 0 "ms", word "both"])

-- `m3 126ms linear(0, 0.059, …, 1.003, 1) 474ms both`: thirty-one component values at the
-- top and sixty-one inside the function.
#guard allows env "animation"
  (spaced [word "m3", dim 126 0 "ms", spring, dim 474 0 "ms", word "both"])

-- The shorthand as the kit writes it now, with the easing in the keyframes:
-- `m-2 94.2ms 180ms both`, and paused at a moment, `m-2 94.2ms -60ms both paused`.
#guard allows env "animation"
  (spaced [word "m-2", dim 942 1 "ms", dim 180 0 "ms", word "both"])
#guard allows env "animation"
  (spaced [word "m-2", dim 942 1 "ms", dim (-60) 0 "ms", word "both", word "paused"])

-- The same two under CSS Animations 2, whose grammar names `<'animation-duration'>` and
-- `<'animation-delay-start'>`: each is that property's grammar without its `#`.
#guard allows env2 "animation"
  (spaced [word "m-2", dim 942 1 "ms", dim 180 0 "ms", word "both"])
#guard allows env2 "animation"
  (spaced [word "m-2", dim 942 1 "ms", dim (-60) 0 "ms", word "both", word "paused"])

-- Three animations in one declaration: the list of `#`.
#guard allows env "animation"
  (spaced [word "m2", dim 942 1 "ms", bezier 1000 1000, dim 180 0 "ms", word "both"] ++
    comma :: ws :: spaced [word "m3", dim 126 0 "ms", spring, dim 474 0 "ms", word "both"] ++
    comma :: ws :: spaced [word "m4", dim 150 0 "ms", bezier 0 0, dim 0 0 "ms", word "both"])

-- The easing of a keyframe: `cubic-bezier(0.333333, 1.567, 0.666667, 1)`, the keyword
-- `linear`, and `linear(0, 1)`.
#guard allows env "animation-timing-function" [bezier 1567 1000]
#guard allows env "animation-timing-function" [word "linear"]
#guard allows env "animation-timing-function" [call "linear" (commas [int 0, int 1])]

-- The rule of reduced motion: `animation-duration: 0s` and `animation-delay: 0s`.
#guard allows env "animation-duration" [dim 0 0 "s"]
#guard allows env "animation-delay" [dim 0 0 "s"]

-- A keyframe: `translate: -60px 0px`, `translate: 0px 0px`, `scale: 0`, `scale: 1`.
#guard allows env "translate" [dim (-60) 0 "px", ws, dim 0 0 "px"]
#guard allows env "translate" [dim 0 0 "px", ws, dim 0 0 "px"]
#guard allows env "scale" [int 0]
#guard allows env "scale" [int 1]

-- `opacity: 0.25`: what `Pose.fade 250` writes by the rule of
-- `Whatwg/Html/Node/SvgMotion.lean`.
#guard allows env "opacity" [num 250 3]

-- Beside every animation of a box: `transform-box: fill-box; transform-origin: center`.
#guard allows env "transform-box" [word "fill-box"]
#guard allows env "transform-origin" [word "center"]

-- A `transform` list of CSS: `translate(10px, 20px) rotate(45deg) scale(1.5)`, and one
-- argument where the second is left out with its comma, `translate(10px)`.
#guard allows env "transform"
  (spaced [call "translate" (commas [dim 10 0 "px", dim 20 0 "px"]),
    call "rotate" [dim 45 0 "deg"], call "scale" [num 15 1]])
#guard allows env "transform" [call "translate" [dim 10 0 "px"]]
#guard allows env "transform" [call "rotate" [int 0]]

-- What the kit writes for the SVG attribute, `translate(10,20) rotate(45)`, is no value of the
-- CSS property: a length needs a unit, and an angle with none is zero alone. The sealed text
-- says so under `svg-syntax`: the attribute is written by another grammar than the property.
#guard !allows env "transform"
  (spaced [call "translate" [int 10, comma, int 20], call "rotate" [int 45]])

/-! ## Controls -/

-- One keyword off: `fil-box`, and `bth` where the animation already has its name.
#guard !allows env "transform-box" [word "fil-box"]
#guard !allows env "animation"
  (spaced [word "m-2", dim 942 1 "ms", dim 180 0 "ms", word "bth"])
#guard !allows env "animation-fill-mode" [word "bth"]

-- A comma missing: inside `cubic-bezier()`, inside `linear()`, between two arguments of
-- `translate()`, and between two animations.
#guard !allows env "animation-timing-function"
  [call "cubic-bezier" [num 333333 6, comma, ws, int 1, ws, num 666667 6, comma, ws, int 1]]
#guard !allows env "animation-timing-function" [call "linear" [int 0, ws, int 1]]
#guard !allows env "transform" [call "translate" [dim 10 0 "px", ws, dim 20 0 "px"]]
#guard !allows env "animation"
  (spaced [word "m2", dim 942 1 "ms", word "both", word "m3", dim 126 0 "ms", word "both"])

-- A part of `||` twice: three times where the grammar has two, and two easings.
#guard !allows env "animation"
  (spaced [word "m2", dim 1 0 "s", dim 2 0 "s", dim 3 0 "s"])
#guard !allows env "animation" (spaced [word "m2", bezier 0 0, bezier 1000 1000])

-- A range: a duration is not negative, and the first number of a pair of `cubic-bezier()` is
-- between zero and one.
#guard !allows env "animation-duration" [dim (-1) 0 "s"]
#guard !allows env "animation-timing-function"
  [call "cubic-bezier" (commas [num 1500 3, int 0, num 500 3, int 1])]

-- A unit: `94.2` with none is no time, and `0` with none is a length and no time.
#guard !allows env "animation-duration" [num 942 1]
#guard allows env "translate" [int 0]
#guard !allows env "animation-delay" [int 0]

-- A name is read ASCII case-insensitively, and a function name too.
#guard allows env "transform-box" [word "Fill-Box"]
#guard allows env "animation-timing-function" [call "LINEAR" (commas [int 0, int 1])]

-- The depth of names. `animation` reaches `cubic-bezier()` through four names:
-- `<single-animation>`, `<easing-function>`, `<cubic-bezier-easing-function>` and
-- `<cubic-bezier()>`. Four unfoldings are enough and three are not.
#guard (env.property "animation").any fun d =>
  admits env d (spaced [word "m2", dim 942 1 "ms", bezier 1000 1000]) 4 &&
    !admits env d (spaced [word "m2", dim 942 1 "ms", bezier 1000 1000]) 3

-- What this slice leaves open: the kit's scrubbed step writes its delay as
-- `calc((300 - var(--t, 0)) * 0.6ms)`. A math function may stand "wherever such a value would
-- be valid" (`math` of CSS Values 4), and that is prose: the basic type `<time>` of this test
-- takes a dimension alone, so the value is refused here.
#guard !allows env "animation"
  (spaced [word "m-2", dim 942 1 "ms",
    call "calc" [.block .paren [int 300, ws, .token (.delim '-'), ws,
      call "var" [word "--t", comma, ws, int 0]], ws, .token (.delim '*'), ws, dim 6 1 "ms"],
    word "both", word "paused"])

/-! ## A tree as a term of Lean

`Definition.leanTerm` writes a tree as the term a generated data module will hold. For each
line below, the first guard pins what it prints for the tree of the sealed line, and the
second holds that text as code: it elaborates to the same tree. -/

/-- The tree of a collected line. -/
def lineTree (module name : String) : Definition :=
  match (corpus ++ corpusPre).find? fun l => l.module == module && l.name == name with
  | some l => tree l.text
  | none => .keyword "unread"

-- `<time [0s,∞]>#`: a bracketed range, and `#`.
#guard (lineTree "css-animations-1" "animation-duration").leanTerm ==
  ".mult (.type \"time\" (some ⟨.finite 0 \"s\", .infinity⟩)) (.hash none)"
#guard lineTree "css-animations-1" "animation-duration" ==
  .mult (.type "time" (some ⟨.finite 0 "s", .infinity⟩)) (.hash none)

-- `cubic-bezier( [ <number [0,1]>, <number> ]#{2} )`: a function, a comma, `#{2}`.
#guard (lineTree "css-easing-2" "cubic-bezier()").leanTerm ==
  ".function \"cubic-bezier\" (.mult (.group (.seq [.type \"number\" " ++
    "(some ⟨.finite 0 \"\", .finite 1 \"\"⟩), .literal ',', .type \"number\" none])) " ++
    "(.hash (some (.exactly 2))))"
#guard lineTree "css-easing-2" "cubic-bezier()" ==
  .function "cubic-bezier" (.mult (.group (.seq [.type "number"
    (some ⟨.finite 0 "", .finite 1 ""⟩), .literal ',', .type "number" none]))
    (.hash (some (.exactly 2))))

-- `linear( [ <number> && <percentage>{0,2} ]# )`: `&&` and `{0,2}`.
#guard (lineTree "css-easing-2" "linear()").leanTerm ==
  ".function \"linear\" (.mult (.group (.all [.type \"number\" none, " ++
    ".mult (.type \"percentage\" none) (.times (.between 0 2))])) (.hash none))"
#guard lineTree "css-easing-2" "linear()" ==
  .function "linear" (.mult (.group (.all [.type "number" none,
    .mult (.type "percentage" none) (.times (.between 0 2))])) (.hash none))

-- `<calc-value> [ [ '*' | / ] <calc-value> ]*`: a quoted delimiter and a literal one.
#guard (lineTree "css-values-4" "<calc-product>").leanTerm ==
  ".seq [.type \"calc-value\" none, .mult (.group (.seq [.group (.one [.quoted \"*\", " ++
    ".literal '/']), .type \"calc-value\" none])) .star]"
#guard lineTree "css-values-4" "<calc-product>" ==
  .seq [.type "calc-value" none, .mult (.group (.seq [.group (.one [.quoted "*",
    .literal '/']), .type "calc-value" none])) .star]

-- `: <ident-token> | : <function-token> <any-value> )`: a function of any name.
#guard (lineTree "css-values-4" "<pseudo-class-selector>").leanTerm ==
  ".one [.seq [.literal ':', .type \"ident-token\" none], " ++
    ".seq [.literal ':', .anyFunction (.type \"any-value\" none)]]"
#guard lineTree "css-values-4" "<pseudo-class-selector>" ==
  .one [.seq [.literal ':', .type "ident-token" none],
    .seq [.literal ':', .anyFunction (.type "any-value" none)]]

-- `<keyframe-selector># { <declaration-list> }`: braces written literally, after a `#` that
-- they are no part of. `[ <'animation-delay-start'> <'animation-delay-end'>? ]#`: the grammar
-- of a property. `( <calc-sum> )`: parentheses written literally.
#guard lineTree "css-animations-1" "<keyframe-block>" ==
  .seq [.mult (.type "keyframe-selector" none) (.hash none),
    .braces (.type "declaration-list" none)]
#guard lineTree "css-animations-2" "animation-delay" ==
  .mult (.group (.seq [.property "animation-delay-start",
    .mult (.property "animation-delay-end") .opt])) (.hash none)
#guard lineTree "css-values-4" "<calc-value>" ==
  .one [.type "number" none, .type "dimension" none, .type "percentage" none,
    .type "calc-keyword" none, .parens (.type "calc-sum" none)]

-- A bound below zero and the two spellings of `-∞`, U+002D and U+2212, which no collected
-- line has: the examples of `numeric-ranges` in prose.
#guard Definition.read "<angle [-90deg, 90deg]>" ==
  some (.type "angle" (some ⟨.finite (-90) "deg", .finite 90 "deg"⟩))
#guard (Definition.type "angle" (some ⟨.finite (-90) "deg", .finite 90 "deg"⟩)).leanTerm ==
  ".type \"angle\" (some ⟨.finite (-90) \"deg\", .finite 90 \"deg\"⟩)"
#guard Definition.read "<length [-∞,∞]>" == some (.type "length" (some ⟨.negInfinity, .infinity⟩))
#guard Definition.read ("<length [" ++ String.singleton (Char.ofNat 0x2212) ++ "∞, ∞]>") ==
  some (.type "length" (some ⟨.negInfinity, .infinity⟩))

/-! ## A writer that is sound against a sealed grammar

The laws of `Whatwg/Css/Values/Admits/Laws.lean` at work, once: a theorem of the kind slice K5
owes for each property the kit writes. -/

/-- `animation-duration` of CSS Animations 1 as a generated data module will hold it. -/
def animationDuration : Definition :=
  .mult (.type "time" (some ⟨.finite 0 "s", .infinity⟩)) (.hash none)

-- It is the tree of the sealed line.
#guard env.property "animation-duration" == some animationDuration

/-- A duration in whole milliseconds, as the component value its text is. -/
def msToken (n : Nat) : Component := .token (.dimension ⟨(n : Rat), none⟩ .integer ['m', 's'])

/-- `<time [0s,∞]>` takes every whole number of milliseconds. -/
theorem time_admits_ms (n : Nat) :
    Basic.dimension timeUnits false (some ⟨.finite 0 "s", .infinity⟩) (msToken n) = true := by
  have hl : (Basic.lookup timeUnits ['m', 's']).isSome = true := by decide
  have hn : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  simp only [msToken, Basic.dimension, hl, Basic.inRange, Basic.atMost, Basic.atLeast, BEq.rfl,
    if_true, hn, decide_true, Bool.and_self]

/-- A writer of durations is sound against the sealed grammar: whatever whole milliseconds it
writes, one or more with a comma between two, `animation-duration` admits the value, in every
environment where `<time>` is the basic type of the time units. -/
theorem durations_admitted (e : Env)
    (h : e.type "time" = some (.basic (Basic.dimension timeUnits false)))
    (ns : List Nat) (hne : ns ≠ []) :
    admits e animationDuration
      (joined [Component.token .comma] (ns.map fun n => [msToken n])) = true := by
  refine admits_hash e rfl (fun eq => hne (List.map_eq_nil_iff.mp eq)) fun v hv => ?_
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hv
  rw [admits_type_basic e h (some ⟨.finite 0 "s", .infinity⟩) [msToken n] 32]
  exact time_admits_ms n

end WhatwgTest.Css
