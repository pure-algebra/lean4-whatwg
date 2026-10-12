import Whatwg.Html.Node.SvgKeys

/-!
# WhatwgTest.Html.SvgKeys

Readers, controls and finite evaluations of the keys of a typed SVG attribute list (slice S6 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-36): `Whatwg/Html/Node/SvgKeys.lean`.

The box here is built as a program builds it: from constructors, with numbers and texts that
are variables. The pass `SvgAttr.allOk` is evaluated at it with every value free: unfolding
the pass drops the values, and what is left reads keys. A reader applies a law at that list, or
at a list that is not known. A control is a list that the pass refuses, or a pair that only a
raw tree can hold.

What this battery does not claim: that a value is right, or that an element stands where its
parent admits it. `WhatwgTest/Html/SvgNode.lean` reads a value's rightness from its type, and
`validIn` judges the structure.
-/

namespace WhatwgTest.Html.SvgKeys

open Whatwg.Html
open Whatwg.Html.SvgAttr
open Whatwg.Svg.Value

/-! ## A key and its name -/

-- The name of each kind of key. A name of the schema is written exactly, with its case.
#guard (Key.attr .viewBox).name == "viewBox" && (Key.attr .stroke_width).name == "stroke-width"
#guard (Key.data "key").name == "data-key"
#guard Key.xmlns.name == "xmlns" && Key.xmlnsXlink.name == "xmlns:xlink"

-- Reader of `Key.name_injective`: two attributes of a `rect` that write one name have one key,
-- whatever their values.
example (p q : SvgAttr .rect) (h : p.toPair.1 = q.toPair.1) : p.key = q.key :=
  Key.name_injective (by rw [← toPair_fst, ← toPair_fst]; exact h)

/-! ## The pass over a list that a program builds -/

/-- The attributes of a filled box with a key, as a program builds them: the numbers and the
texts are the caller's. -/
def boxAttrs (x y : Int) (w h : Nat) (role key : String) : List (SvgAttr .rect) :=
  [.attr .«class» ("e4-fill-" ++ role), .attr .x (.user (.ofInt x)), .attr .y (.user (.ofInt y)),
    .attr .width (.user (.ofNat w)), .attr .height (.user (.ofNat h)),
    .attr .fill "var(--ink)", .attr .fill_opacity "0.8", .data "key" key]

/-- The pass holds of every box. Unfolding the pass drops each value, and the kernel evaluates
what is left: a closed term that reads keys. -/
theorem allOk_boxAttrs (x y : Int) (w h : Nat) (role key : String) :
    allOk (boxAttrs x y w h role key) = true := by
  simp only [allOk, boxAttrs, okFrom]
  decide +kernel

-- Reader of the law `svgAttrsOk_toPairs`: the checker's test of the pairs that a box writes
-- holds of every box. No name is decoded and no value is printed.
example (x y : Int) (w h : Nat) (role key : String) :
    Content.svgAttrsOk .rect ((boxAttrs x y w h role key).map toPair) = true :=
  (svgAttrsOk_toPairs _).trans (allOk_boxAttrs x y w h role key)

-- Reader of `allOk_iff` at a list that is not known: an attribute list of a `rect` that
-- passes holds no `d`, whatever else it holds.
example (attrs : List (SvgAttr .rect)) (h : allOk attrs = true) (p : PathData) :
    SvgAttr.attr .d p ∉ attrs := by
  intro hmem
  have hok : Key.okOn .rect (.attr .d) = true := ((allOk_iff attrs).mp h).1 _ hmem
  exact absurd hok (by decide +kernel)

/-! ## What the pass refuses -/

-- Control: an attribute of the schema repeats, with another attribute between the two.
#guard !allOk (t := .rect) [.attr .x (.user 1), .attr .y (.user 2), .attr .x (.user 3)]

-- Control: a data key repeats.
#guard !allOk (t := .rect) [.data "key" "a", .data "key" "b"]

-- Control: a namespace declaration repeats. The two declarations are two keys, so one of each
-- passes.
#guard !allOk (t := .svg) [.xmlns, .xmlns]
#guard allOk (t := .svg) [.xmlns, .xmlnsXlink]

-- Control: an attribute that the element does not take. `d` on `rect` has the type of path
-- data, and the pass refuses its key.
#guard !allOk (t := .rect) [.attr .d .none]

-- Control: a data key with an upper-case letter, and the empty data key.
#guard !allOk (t := .rect) [.data "Key" "v"]
#guard !allOk (t := .rect) [.data "" "v"]

-- An attribute of the schema and a data key of the same text are two keys: `x` and `data-x`.
#guard allOk (t := .rect) [.attr .x (.user 1), .data "x" "1"]

/-! ## Where the law stops -/

-- Control: the law is about the pairs that a typed list writes. A raw pair may declare another
-- namespace, and the checker refuses it. A typed `xmlns` holds no value, so the pass asks none.
#guard !Content.svgAttrsOk .svg [("xmlns", "http://example.org/")]

/-! ## A list with no repeat -/

-- Reader of `eraseDups_length_eq_iff` at numbers: two numbers that keep their count after
-- duplicates are erased are different.
example (a b : Nat) (h : [a, b].eraseDups.length = 2) : a ≠ b :=
  fun hab => (List.nodup_cons.mp ((eraseDups_length_eq_iff [a, b]).mp h)).1
    (List.mem_singleton.mpr hab)

end WhatwgTest.Html.SvgKeys
