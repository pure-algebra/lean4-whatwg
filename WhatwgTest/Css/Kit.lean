import WhatwgTest.Css.Values
import WhatwgTest.Html.SvgMotion

/-!
# WhatwgTest.Css.Kit

Owner: what the picture kit writes, judged by the sealed grammars (a first step of slice K5 of
`docs/CSS-PACKAGE-PLAN.md`; slice S22 of `docs/SVG-PACKAGE-PLAN.md`; rulings CS-5 and CS-9).

Until slice S22 the kit wrote text, and `WhatwgTest/Css/Values.lean` judged component values
that a hand had built to match that text. Now the kit builds component values
(`Whatwg/Html/Node/SvgMotion.lean` on `Whatwg/Css/Syntax/Build.lean`), so the value that is
judged here is the kit's own: nothing is read and nothing is built again.

The grammars are those of `WhatwgTest/Css/Values.lean`: the `Value:` lines and the productions
of the sealed modules, read by `Definition.read`, in the environment `env` of that module. The
steps are those of `WhatwgTest/Html/SvgMotion.lean`: the consumer's step of five things, and a
step with a track of each kind of change.

What is judged, and what comes out.

1. *Every declaration that the two steps write*, under each way of playing them that no
   property scrubs: in the rules of the sheet, the keyframes among them, and on each thing.
   Each declaration of a property that a sealed module defines is admitted: `translate`,
   `scale`, `opacity`, `animation`, `animation-timing-function`, `animation-duration`,
   `animation-delay`, `transform-box`, `transform-origin`.
2. *Three properties have no sealed grammar*: `stroke-dashoffset`, `stroke-dasharray` and `d`
   are properties of SVG 2, whose chapters on painting and on paths are not among the sealed
   modules that this test reads. Nothing judges them here.
3. *A scrubbed step is refused*, in its `animation` and in nothing else: the delay is
   `calc((300 - var(--t, 0)) * 0.6ms)`, and `<time>` as this test reads it is a dimension token
   alone. Section 8 of the plan says why this is the grammar as written and not a fault of the
   kit: that a math function may stand where its type would, and that a value holding `var()`
   is judged after the reference is replaced, are prose of CSS Values 4 and of CSS Variables 1.
   Slice K5 has to model both.
4. *The names of the rules*: the name of each `@keyframes` rule is a `<keyframes-name>`, each
   of its keyframes stands under a `<keyframe-selector>`, and the query of the rule of reduced
   motion is a `<media-query>` of Media Queries 5 whose value is one that its descriptor lists.
5. *Controls*: a length with no unit, a size with a unit, an opacity that is a keyword, an
   animation with two names, a keyframe at 150 per cent, and a query with a value that the
   descriptor does not list are refused.
6. *One theorem*: `fade_admitted`. The opacity that the kit writes for any pose is a value of
   `opacity`, for every count of thousandths and in every environment that reads `<number>` as
   the number token. It is of the kind that slice K5 owes for each property.

What this module does not claim. That a browser takes or refuses any of these values. That the
environment built here is the one a generated data module will hold. A theorem for `translate`,
`scale` and `animation`: the laws of a juxtaposition with an optional part, of `{A,B}` and of
`||` at eight parts that they need are not all in `Whatwg/Css/Values/Admits/Laws.lean` yet, and
a guard is a finite evaluation at the steps of this file.
-/

namespace WhatwgTest.Css.Kit

open Whatwg.Html
open Whatwg.Svg.Scene (Motion Pose Easing Track)
open Whatwg.Css.Values (Env Definition admits Meaning admits_one admits_type_production
  admits_type_basic)
open Whatwg.Css.Syntax (Component Value Prelude)
open WhatwgTest.Html.SvgMotion (Ease fiveStep everyChange play filed plays)

/-- Every declaration of a rule and of its child rules, to a depth. A sheet of the kit has two
levels. -/
def declsOf : Nat → Css.Rule → Css.Decls
  | 0, _ => []
  | n + 1, r => r.decls ++ r.rules.flatMap (declsOf n)

/-- **Every declaration that a step writes** under a way of playing it: those of its rules, and
those it gives each of its things. -/
def written (m : Motion String) (p : Play) : Css.Decls :=
  (m.rules p).flatMap (declsOf 3) ++ m.keys.flatMap fun k => m.given k p

/-- **What the sealed grammar of a declaration's property says of its value**: admitted or
refused, and nothing where no sealed module defines the property. -/
def judge (d : Css.Decl) : Option Bool :=
  (env.property (String.ofList d.name)).map fun g => admits env g d.value

/-- The names of the properties of a row of declarations, each once. -/
def properties (ds : Css.Decls) : List String := (ds.map fun d => String.ofList d.name).eraseDups

/-- The two steps under each way of playing them that no property scrubs. -/
def unscrubbed : Css.Decls :=
  (plays.filter fun p => p.scrub.isNone).flatMap fun p =>
    [fiveStep, everyChange].flatMap fun m => written m p

/-- The two steps scrubbed by `--t`, the inline way and by the sheet. -/
def scrubbed : Css.Decls :=
  [play.scrubbed, filed.scrubbed].flatMap fun p =>
    [fiveStep, everyChange].flatMap fun m => written m p

/-! ## Every declaration of a step that no property scrubs -/

-- Two steps under four ways of playing them: 256 declarations, and the sealed grammars refuse
-- none.
#guard unscrubbed.length == 256 && unscrubbed.all fun d => judge d != some false

-- The properties that a sealed module defines, each admitted wherever a step writes it.
#guard properties (unscrubbed.filter fun d => judge d == some true) ==
  ["translate", "animation-timing-function", "scale", "animation-duration", "animation-delay",
    "animation", "transform-box", "transform-origin", "opacity"]

-- The properties that no sealed module defines: three of SVG 2. Nothing judges them here.
#guard properties (unscrubbed.filter fun d => (judge d).isNone) ==
  ["stroke-dashoffset", "stroke-dasharray", "d"]

-- The four values that the brief of slice K5 names, each as the kit builds it: an opacity, a
-- shift on a grid of eight, a size below nothing and past its end, and the animation of a
-- thing with two tracks, opened in the middle of the step and paused.
#guard [(Pose.fade 250).decl, (Pose.fade 0).decl, (Pose.shift ⟨-60, 7⟩).decl 8,
    (Pose.grow (-50)).decl, (Pose.grow 1567).decl].all fun d => judge d == some true

#guard ((everyChange.decls "c" { play with opened := 400, paused := true }).head?.map fun d =>
    (d.css, judge d)) ==
  some ("animation: m-3 199.8ms -60ms both paused, m-4 180ms 120ms both paused", some true)

-- Each of the consumer's seven easings, as the value the kit builds for it, is an
-- `<easing-function>`: the function `linear`, the keyword `linear`, and `cubic-bezier`.
#guard Ease.all.all fun e => admits env (.type "easing-function" none) e.kit.value

/-! ## A step that one number scrubs -/

-- The grammar refuses the `animation` of each thing of a scrubbed step, and nothing else of
-- it: thirty declarations of 128.
#guard scrubbed.length == 128 &&
  properties (scrubbed.filter fun d => judge d == some false) == ["animation"] &&
  (scrubbed.filter fun d => judge d == some false).length == 30

/-- The track of the route of the port's step: drawn from 300 per mille on, for 157. -/
def route : Track String :=
  { key := "a c", change := .reveal 0 1000, timing := { delay := 300, duration := 157 } }

-- What is refused is the delay. The same animation with the delay as a time is admitted, and
-- the `calc()` alone is no `<time>` of this test.
#guard judge (.of "animation" (Motion.animation "m-2" route play.scrubbed)) == some false &&
  judge (.of "animation"
    (Motion.animation "m-2" route { play with opened := 400, paused := true })) == some true &&
  judge (.of "animation-delay" [play.scrubbed.delay 300]) == some false

-- The declaration that puts a scrubbed step at a moment is of a custom property, which takes
-- any value: no grammar judges it.
#guard (play.scrubbed.at 400).map judge == [none]

/-! ## The names of the rules -/

/-- The value is one of the type, in the environment of the kit's properties. -/
def typed (name : String) (v : Value) : Bool := admits env (.type name none) v

-- The name of each `@keyframes` rule of the two steps is a `<keyframes-name>`, and each of its
-- keyframes stands under a `<keyframe-selector>`.
#guard [fiveStep, everyChange].all fun m => (m.keyframeRules play).all fun r =>
  r.name? == some "keyframes" && typed "keyframes-name" r.prelude &&
    r.rules.all fun k => typed "keyframe-selector" k.prelude

-- The selectors of a keyframe that the builders give: the two ends and a per cent between
-- them. A per cent past the end is refused by the range of the grammar, and a name that is a
-- keyword of every property is no name of an animation.
#guard typed "keyframe-selector" Prelude.from && typed "keyframe-selector" Prelude.to &&
  typed "keyframe-selector" (Prelude.percent 50) &&
  !typed "keyframe-selector" (Prelude.percent 150) && !typed "keyframes-name" [.ident "inherit"]

/-- The environment of a media query: Media Queries 5, and CSS Values 4 for its basic types. -/
def media : Env := envOf ["mediaqueries-5", "css-values-4"]

/-- The value grammar of the media feature `prefers-reduced-motion`, as its descriptor block
has it. -/
def reducedMotion : Definition :=
  tree (((corpus.find? fun l => l.kind == "descdef" && l.name == "prefers-reduced-motion").map
    fun l => l.text).getD "")

-- The query of the rule of reduced motion is a `<media-query>`, and its value is one that the
-- descriptor of the feature lists: `no-preference | reduce`.
#guard admits media (.type "media-query" none) Play.reducedQuery &&
  reducedMotion.print == "no-preference | reduce" && admits media reducedMotion [.ident "reduce"]

-- A control: a value that the descriptor does not list. The grammar of a query takes any
-- identifier as the value of a feature, so it is the descriptor that refuses it.
#guard admits media (.type "media-query" none)
    (Prelude.feature "prefers-reduced-motion" [.ident "reduced"]) &&
  !admits media reducedMotion [.ident "reduced"]

/-! ## Controls -/

-- What the kit could have built wrong, each refused by the grammar of its property: a shift
-- with no unit, a size with a unit, an opacity that is a keyword, an animation with two names.
#guard ([.of "translate" (Value.spaced [.int (-60), .int 7]), .of "scale" [.px 1],
    .of "opacity" [.ident "fill-box"],
    .of "animation" (Value.spaced [.ident "m-0", .ident "m-1", .ms 270])] : Css.Decls).all
  fun d => judge d == some false

-- A shift of nothing needs no unit: `0` is a length.
#guard judge (.of "translate" (Value.spaced [.int 0, .int 0])) == some true

/-! ## A writer that is sound against a sealed grammar -/

/-- `opacity` of CSS Color 4 as a generated data module will hold it. -/
def opacity : Definition := .type "opacity-value" none

/-- `<opacity-value>` of CSS Color 4. -/
def opacityValue : Definition := .one [.type "number" none, .type "percentage" none]

-- They are the trees of the sealed lines.
#guard env.property "opacity" == some opacity &&
  (match env.type "opacity-value" with
    | some (.production d) => d == opacityValue
    | _ => false)

/-- **The opacity that the kit writes is a value of `opacity`**, for every count of thousandths:
whatever a track fades a thing to, below nothing and past the whole included. It holds in every
environment where `<opacity-value>` is the sealed production and `<number>` is the number
token. -/
theorem fade_admitted (e : Env)
    (hv : e.type "opacity-value" = some (.production opacityValue))
    (hn : e.type "number" = some (.basic Whatwg.Css.Values.Basic.number)) (shown : Int) :
    admits e opacity (Pose.fade shown).decl.value = true := by
  show admits e (.type "opacity-value" none) [Component.thousandths shown] (31 + 1) = true
  rw [admits_type_production e hv, opacityValue, admits_one, List.any_cons,
    admits_type_basic e hn]
  rfl

end WhatwgTest.Css.Kit
