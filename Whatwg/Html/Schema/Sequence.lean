import Whatwg.Html.Schema.Tags

/-!
# Whatwg.Html.Schema.Sequence

The ordered content models as regular expressions over child tags
(ruling HP-13, slice H7.1): the type the generated `Tag.seq?` table uses.
`base except` is one child the element's base admits other than the named
tags; text is the tag `pcdata`. `render` spells a sequence for messages.
-/

namespace Whatwg.Html.Schema

/-- A regular expression over child tags. -/
inductive Seq where
  | eps
  | empty
  | tag (t : Tag)
  | base (except : List Tag)
  | seq (a b : Seq)
  | alt (a b : Seq)
  | star (a : Seq)
  | opt (a : Seq)
  | plus (a : Seq)
  deriving DecidableEq, Repr, Inhabited

namespace Seq

/-- The sequence in the usual notation, for messages. -/
def render : Seq → String
  | .eps => "ε"
  | .empty => "∅"
  | .tag t => t.variantName
  | .base [] => "content"
  | .base ex => "content-except-" ++ "-".intercalate (ex.map (·.variantName))
  | .seq a b => a.render ++ " " ++ b.render
  | .alt a b => "(" ++ a.render ++ " | " ++ b.render ++ ")"
  | .star a => "(" ++ a.render ++ ")*"
  | .opt a => "(" ++ a.render ++ ")?"
  | .plus a => "(" ++ a.render ++ ")+"

end Seq
end Whatwg.Html.Schema
