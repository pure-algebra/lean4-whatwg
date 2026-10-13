import Whatwg.Html.Node.SvgMotion
import Whatwg.Css.Syntax.Build.Laws

/-!
# Whatwg.Html.Node.SvgMotion.Laws

Owner: what the values of a step are, as values of the tree of CSS (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; a first step of slice K5 of `docs/CSS-PACKAGE-PLAN.md`).

`Whatwg/Html/Node/SvgMotion.lean` builds every value that a step writes. This module says of
those values what `Whatwg/Css/Syntax/Build/Laws.lean` says of the builders: each can be written
(`Value.writable`, the premise under which the tokenizer reads the text back), and its text
holds no comment (`Value.quiet`). The laws are for every easing, every count, every pose and
every way of playing a step, and not for the steps of a test.

- `Easing.value_writable`, `Easing.value_quiet`: an easing, whatever its stops and its heights.
- `Css.writable_milliseconds`, `Css.writable_signedMilliseconds`, `Css.writable_pixels`: a time
  and a length of any count of thousandths.
- `Play.delay_writable`, `Play.delay_quiet`: the delay of an animation, a time or the `calc()`
  of a scrubbed step.
- `Pose.decl_writable`, `Pose.decl_quiet`: the value of a pose.
- `Motion.animation_writable`, `Motion.animation_quiet`: one animation of the `animation`
  property.

What a caller gives. Two names come from the caller: the stem of a step, which is in the name
of each rule, and the custom property that scrubs a step. A law that writes one asks that it be
a name the tokenizer can give: at least one code point, and no U+0000 (`isNameValue`). A caller
shows it of its own stem with `by decide`.

What this module does not claim. That a sheet or a row of declarations is writable as a whole:
`Css.Sheet.writable` and `Css.Decls.writable` compute that, and
`WhatwgTest/Html/SvgMotion.lean` reads them at the steps of the port. That the value of a
change of shape is writable: `Pose.decl_writable` leaves a shape out, since its path data is a
text that core writes from numbers, and that such a text holds no U+0000 is not proved here; a
guard reads it. That a value is one of its property: `WhatwgTest/Css/Kit.lean` judges that
against the sealed grammars.

Every theorem of this module depends on `propext`, `Quot.sound` and `Classical.choice` at
most.
-/

namespace Whatwg.Html

open Whatwg.Svg.Scene (Easing Pose Track Motion)
open Whatwg.Css.Syntax (Component Value Calc isNameValue isDecimal_mkRat_thousand)

namespace Css

/-- **A length of any count of thousandths of a pixel is writable.** -/
theorem writable_pixels (n : Int) : (pixels n).writable = true :=
  (Component.writable_px _).trans (isDecimal_mkRat_thousand n)

/-- **A time of any share of any step is writable.** -/
theorem writable_milliseconds (perMille step : Nat) :
    (milliseconds perMille step).writable = true :=
  (Component.writable_ms _).trans (isDecimal_mkRat_thousand _)

/-- **A time before or after the start of a step is writable.** -/
theorem writable_signedMilliseconds (perMille : Int) (step : Nat) :
    (signedMilliseconds perMille step).writable = true :=
  (Component.writable_ms _).trans (isDecimal_mkRat_thousand _)

/-- A third to six places is writable. -/
theorem writable_third : third.writable = true := by decide +kernel

/-- Two thirds to six places is writable. -/
theorem writable_twoThirds : twoThirds.writable = true := by decide +kernel

/-- Each of a row of counts of thousandths is writable. -/
theorem writable_thousandths_of_mem {values : List Int} :
    ∀ c ∈ values.map Component.thousandths, c.writable = true := fun c hc => by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
  exact Component.writable_thousandths v

/-- Each of a row of counts of thousandths is quiet. -/
theorem quiet_thousandths (values : List Int) :
    (values.map Component.thousandths).all Component.quiet = true :=
  List.all_eq_true.mpr fun c hc => by
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
    rfl

/-- `linear(…)` of writable component values is writable. -/
theorem writable_linear {cs : List Component} (h : ∀ c ∈ cs, c.writable = true) :
    Value.writable [.call "linear" (Value.commas cs)] = true :=
  (Value.writable_singleton _).trans
    (Component.writable_call (by decide +kernel) (by decide +kernel) (Value.writable_commas h))

/-- `linear(…)` is quiet exactly when each of its arguments is. -/
theorem quiet_linear (cs : List Component) :
    Value.quiet [.call "linear" (Value.commas cs)] = cs.all Component.quiet := by
  rw [Value.quiet_singleton, Component.quiet_call, Value.quiet_commas]

end Css

/-- **Every easing is written as a value that can be written**: `linear(…)` of any stops, the
keyword `linear`, and `cubic-bezier(…)` of any two heights. -/
theorem _root_.Whatwg.Svg.Scene.Easing.value_writable (e : Easing) :
    e.value.writable = true := by
  fun_cases Easing.value e
  · decide +kernel
  · rename_i v
    exact Css.writable_linear (cs := [v, v].map Component.thousandths)
      Css.writable_thousandths_of_mem
  · decide +kernel
  · exact Css.writable_linear Css.writable_thousandths_of_mem
  · rename_i y1 y2
    refine (Value.writable_singleton _).trans
      (Component.writable_call (by decide +kernel) (by decide +kernel)
        (Value.writable_commas fun c hc => ?_))
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Css.writable_third
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Component.writable_thousandths y1
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Css.writable_twoThirds
    · rw [List.mem_singleton.mp hc]
      exact Component.writable_thousandths y2

/-- **The text of every easing holds no comment.** -/
theorem _root_.Whatwg.Svg.Scene.Easing.value_quiet (e : Easing) : e.value.quiet = true := by
  fun_cases Easing.value e
  · rfl
  · rfl
  · rfl
  · exact (Css.quiet_linear _).trans (Css.quiet_thousandths _)
  · rfl

namespace Play

/-- **The delay of an animation is writable**: a time, and in a scrubbed step `calc()` of the
custom property, where the name of the property holds no U+0000. -/
theorem delay_writable (play : Play) (delay : Nat)
    (h : ∀ p, play.scrub = some p → (p.toList.all fun c => c.toNat != 0) = true) :
    (play.delay delay).writable = true := by
  unfold Play.delay
  split
  · exact Css.writable_signedMilliseconds _ _
  · rename_i property hp
    refine Component.writable_calc ?_
    show ((Component.int delay).writable &&
      (Component.var property [.int play.opened]).writable &&
      (Component.ms (mkRat play.step 1000)).writable) = true
    rw [Component.writable_int,
      Component.writable_var (h property hp)
        ((Value.writable_singleton _).trans (Component.writable_int _)),
      Component.writable_ms, isDecimal_mkRat_thousand]
    rfl

/-- **The text of the delay of an animation holds no comment.** -/
theorem delay_quiet (play : Play) (delay : Nat) : (play.delay delay).quiet = true := by
  unfold Play.delay
  split
  · rfl
  · rename_i property _
    rw [Component.quiet_calc]
    show ((Component.int delay).quiet && (Component.var property [.int play.opened]).quiet &&
      (Component.ms (mkRat play.step 1000)).quiet) = true
    rw [Component.quiet_var]
    rfl

end Play

/-- **The value of a pose that is no shape is writable**, on any grid: a shift, a size, a part
revealed and an opacity are numbers and lengths of counts of thousandths. -/
theorem _root_.Whatwg.Svg.Scene.Pose.decl_writable (p : Pose) (grid : Nat)
    (h : ∀ segments, p ≠ .shape segments) : Value.writable (p.decl grid).value = true := by
  cases p with
  | shift step =>
    refine Value.writable_spaced fun c hc => ?_
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Css.writable_pixels _
    · rw [List.mem_singleton.mp hc]
      exact Css.writable_pixels _
  | grow size => exact (Value.writable_singleton _).trans (Component.writable_thousandths size)
  | reveal part => exact (Value.writable_singleton _).trans (Component.writable_int _)
  | fade shown => exact (Value.writable_singleton _).trans (Component.writable_thousandths shown)
  | shape segments => exact absurd rfl (h segments)

/-- **The text of the value of every pose holds no comment**, a shape among them. -/
theorem _root_.Whatwg.Svg.Scene.Pose.decl_quiet (p : Pose) (grid : Nat) :
    Value.quiet (p.decl grid).value = true := by
  cases p <;> rfl

section

variable {κ : Type}

/-- **One animation of the `animation` property is writable**, where the name of its rule is
one the tokenizer can give and the name of a scrubbing property holds no U+0000. -/
theorem _root_.Whatwg.Svg.Scene.Motion.animation_writable (name : String) (tr : Track κ)
    (play : Play) (hn : isNameValue name.toList = true)
    (hs : ∀ p, play.scrub = some p → (p.toList.all fun c => c.toNat != 0) = true) :
    (Motion.animation name tr play).writable = true := by
  refine Value.writable_spaced fun c hc => ?_
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact (Component.writable_ident name).trans hn
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Css.writable_milliseconds _ _
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Play.delay_writable play _ hs
    · rw [List.mem_singleton.mp hc]
      decide +kernel
  · split at hc
    · rw [List.mem_singleton.mp hc]
      decide +kernel
    · exact nomatch hc

/-- **The text of one animation holds no comment.** -/
theorem _root_.Whatwg.Svg.Scene.Motion.animation_quiet (name : String) (tr : Track κ)
    (play : Play) : (Motion.animation name tr play).quiet = true := by
  rw [Motion.animation, Value.quiet_spaced]
  refine List.all_eq_true.mpr fun c hc => ?_
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Play.delay_quiet play _
    · rw [List.mem_singleton.mp hc]
      rfl
  · split at hc
    · rw [List.mem_singleton.mp hc]
      rfl
    · exact nomatch hc

end

end Whatwg.Html
