/-!
# Whatwg.Svg.Scene.Join

Owner: the join of two lists by key (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-61).

A picture of a program changes when the program does. Each thing that is drawn has a key, the
name of what it draws. The join of the old list and the new one by key says what happens to
each thing: a new key *enters*, a kept key *updates* from its old thing to its new one, and an
old key *exits*. This is the data join of d3's selections, as lean4-effect4's
`tools/Tools/View/Motion.lean` has it, for a key of any type with a lawful equality test.

The laws are in `Whatwg/Svg/Scene/Join/Laws.lean`. This layer is under the strict ceiling and
has no number in it.
-/

namespace Whatwg.Svg.Scene

/-- The three selections of a join: the new things that enter, the kept ones as pairs of the old
and the new, and the old things that exit. -/
structure Join (α : Type) where
  enter : List α
  update : List (α × α)
  exit : List α
  deriving Repr

/-- **The join by key** of an old list and a new one. A new thing whose key no old thing has
enters. A new thing whose key an old thing has updates the first such old thing. An old thing
whose key no new thing has exits. -/
def join {α κ : Type} [BEq κ] (key : α → κ) (old new : List α) : Join α where
  enter := new.filter fun n => !(old.any fun o => key o == key n)
  update := new.filterMap fun n => (old.find? fun o => key o == key n).map (·, n)
  exit := old.filter fun o => !(new.any fun n => key n == key o)

/-- The keys of a list are distinct: no two of its things have one key. -/
def Distinct {α κ : Type} (key : α → κ) (l : List α) : Prop := (l.map key).Nodup

end Whatwg.Svg.Scene
