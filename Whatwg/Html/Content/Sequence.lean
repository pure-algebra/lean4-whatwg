import Whatwg.Html.Content.Context
import Whatwg.Html.Node.Raw

/-!
# Whatwg.Html.Content.Sequence

The ordered content models, checked (ruling HP-13, slice H7.1). An
element whose reading is a sequence (`Tag.seq?`) requires the tags of its
children, in order, to match a regular expression over tags; the match is
by Brzozowski derivatives, so it is total and the kernel evaluates it.
Text counts as the tag `pcdata`; a comment is not a child of the sequence;
where the sentence intermixes script-supporting elements, they are removed
before matching. `base except` accepts one tag the children's base admits
other than the named ones, so `flow content` in a sentence is one child of
the flow base.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode)

namespace Seq

/-- The sequence accepts the empty list. -/
def nullable : Seq → Bool
  | .eps => true
  | .empty => false
  | .tag _ => false
  | .base _ => false
  | .seq a b => nullable a && nullable b
  | .alt a b => nullable a || nullable b
  | .star _ => true
  | .opt _ => true
  | .plus a => nullable a

/-- The derivative by one tag, with `base` the children's base. -/
def deriv (base : Tag → Bool) : Seq → Tag → Seq
  | .eps, _ => .empty
  | .empty, _ => .empty
  | .tag other, t => if t == other then .eps else .empty
  | .base ex, t => if base t && !ex.contains t then .eps else .empty
  | .seq a b, t => .alt (.seq (deriv base a t) b) (if nullable a then deriv base b t else .empty)
  | .alt a b, t => .alt (deriv base a t) (deriv base b t)
  | .star a, t => .seq (deriv base a t) (.star a)
  | .opt a, t => deriv base a t
  | .plus a, t => .seq (deriv base a t) (.star a)

/-- The sequence accepts the list of tags. -/
def accepts (base : Tag → Bool) (s : Seq) (ts : List Tag) : Bool :=
  nullable (ts.foldl (deriv base) s)

end Seq

/-- The tag a raw node counts as in a sequence: its element tag, `pcdata`
for text and entities, none for a comment or an unknown name. -/
def RawNode.tag? : RawNode → Option Tag
  | .element name _ _ => Tag.ofName? name
  | .text _ => some .pcdata
  | .entity _ => some .pcdata
  | .comment _ => none

/-- The tags of a child list, comments dropped. -/
def childTags (children : List RawNode) : List Tag := children.filterMap RawNode.tag?

/-- The children of an element of tag `t`, checked at the children's context
`c`, follow the element's ordered model; trivially so when it has none. -/
def seqOk (c : Ctx) (t : Tag) (children : List RawNode) : Bool :=
  match t.seq? with
  | none => true
  | some (s, interleave) =>
    let ts := childTags children
    let ts := if interleave then ts.filter (fun c => !Cats.scriptSupporting c) else ts
    Seq.accepts c.base.contains s ts

/-- Why the children do not follow the model, for messages. -/
def seqProblem? (c : Ctx) (t : Tag) (children : List RawNode) : Option String :=
  match t.seq? with
  | none => none
  | some (s, _) =>
    if seqOk c t children then none
    else some ("the children of <" ++ t.markupText ++ "> do not follow its content model: " ++ s.render)

theorem seqOk_of_none (c : Ctx) (t : Tag) (h : t.seq? = none) (children : List RawNode) :
    seqOk c t children = true := by
  simp [seqOk, h]

/-- The tags with a sequence at the pin. -/
theorem sequenced_tags : Tag.all.filter (fun t => (Tag.seq? t).isSome) =
    [.html, .head, .hgroup, .dl, .figure, .picture, .video, .audio, .table, .select, .optgroup, .fieldset, .details] := by
  decide +kernel

end Whatwg.Html.Content
