import Whatwg.Html.Content.Context

/-!
# Whatwg.Html.Content.Admission

Admission as the obligation the typed tree takes: `Admits ctx t` is
`ctx.admits t = true`, decidable by evaluation, so a use site closes it with
`decide` or the `admits` tactic. What a proof of `Admits ctx t` means: the
tag `t` may stand at the position `ctx` under the readings of the standard
at the pin (`Whatwg.Html.Schema.Readings`).
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-- The admission test, under the name the rest of the library uses. -/
def admits (ctx : Ctx) (child : Tag) : Bool := ctx.admits child

/-- Admission as a proposition. -/
def Admits (ctx : Ctx) (child : Tag) : Prop := admits ctx child = true

instance instDecidableAdmits (ctx : Ctx) (child : Tag) : Decidable (Admits ctx child) :=
  inferInstanceAs (Decidable (admits ctx child = true))

theorem admits_eq (ctx : Ctx) (child : Tag) : admits ctx child = ctx.admits child := rfl

/-- The empty base admits nothing, with no extras. -/
theorem not_admits_nothing (x : Exclusions) (child : Tag) : ¬ Admits ⟨.nothing, x, []⟩ child := by
  simp only [Admits, admits, Ctx.admits, Base.contains, nothing_empty, List.contains_nil,
    Bool.or_self, Bool.false_and, Bool.false_eq_true, not_false_eq_true]

end Whatwg.Html.Content
